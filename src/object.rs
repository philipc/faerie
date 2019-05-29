use crate::artifact::{
    self, Artifact, DataType, Decl, DefinedDecl, ImportKind, LinkAndDecl, Reloc, Scope, SectionKind,
};
use object_write::{
    Binding, Object, Relocation, RelocationKind, RelocationSubkind, Section, SectionId,
    SectionKind as ObjectSectionKind, StandardSection, StandardSegment, Symbol, SymbolId,
    SymbolKind, Visibility,
};
use std::collections::HashMap;
use string_interner::DefaultStringInterner;
use target_lexicon::BinaryFormat;

// interned string idx
type StringIndex = usize;

struct State {
    object: Object,
    // Artifact refers to everything by name, so we need to keep a map from names to
    // sections/symbols.
    strings: DefaultStringInterner,
    sections: HashMap<StringIndex, (SectionId, u64)>,
    symbols: HashMap<StringIndex, SymbolId>,
}

impl State {
    fn new(artifact: &Artifact, format: BinaryFormat) -> Self {
        let object = Object::new(format, artifact.target.architecture);
        State {
            object,
            strings: DefaultStringInterner::default(),
            sections: HashMap::default(),
            symbols: HashMap::default(),
        }
    }

    fn definition(&mut self, name: &str, data: &[u8], decl: &artifact::DefinedDecl) {
        let string_id = self.strings.get_or_intern(name);
        let (section_id, offset) = match decl {
            DefinedDecl::Function(d) => {
                let section = StandardSection::Text;
                let align = d.get_align().unwrap_or(16) as u64;
                self.object
                    .add_subsection(section, name.as_bytes(), data, align)
            }
            DefinedDecl::Data(d) => {
                let section = match d.get_datatype() {
                    DataType::Bytes => {
                        if d.is_writable() {
                            StandardSection::Data
                        } else {
                            StandardSection::ReadOnlyData
                        }
                    }
                    DataType::String => StandardSection::ReadOnlyString,
                };
                let align = d.get_align().unwrap_or(1) as u64;
                self.object
                    .add_subsection(section, name.as_bytes(), data, align)
            }
            DefinedDecl::Section(d) => {
                let segment = match d.kind() {
                    SectionKind::Text => StandardSegment::Text,
                    SectionKind::Data => StandardSegment::Data,
                    SectionKind::Debug => StandardSegment::Debug,
                };
                let segment_name = self.object.segment_name(segment).to_vec();
                // TODO: this behavior should be deprecated, but we need to warn users!
                let kind = if name == ".debug_str" || name == ".debug_line_str" {
                    ObjectSectionKind::OtherString
                } else {
                    match d.get_datatype() {
                        DataType::Bytes => ObjectSectionKind::Other,
                        DataType::String => ObjectSectionKind::OtherString,
                    }
                };
                let name = if self.object.format == BinaryFormat::Macho && name.starts_with('.') {
                    format!("__{}", &name[1..]).into_bytes()
                } else {
                    name.as_bytes().to_vec()
                };
                let align = d.get_align().unwrap_or(1) as u64;
                let section = Section::new(segment_name, name, kind, data.to_vec(), align);
                let section_id = self.object.add_section(section);
                (section_id, 0)
            }
        };
        self.sections.insert(string_id, (section_id, offset));

        fn scope_binding(s: Scope) -> Binding {
            match s {
                Scope::Local => Binding::Local,
                Scope::Global => Binding::Global,
                Scope::Weak => Binding::Weak,
            }
        }
        fn convert_visibility(v: artifact::Visibility) -> Visibility {
            match v {
                artifact::Visibility::Default => Visibility::Default,
                artifact::Visibility::Hidden => Visibility::Hidden,
                artifact::Visibility::Protected => Visibility::Protected,
            }
        }

        // Always add a section symbol in case relocations need it.
        let mut symbol_id = self.object.add_section_symbol(section_id);

        match decl {
            DefinedDecl::Function(d) => {
                symbol_id = self.object.add_symbol(Symbol {
                    name: self.abi_name(name),
                    value: offset,
                    size: data.len() as u64,
                    binding: scope_binding(d.get_scope()),
                    visibility: convert_visibility(d.get_visibility()),
                    kind: SymbolKind::Text,
                    section: Some(section_id),
                });
            }
            DefinedDecl::Data(d) => {
                symbol_id = self.object.add_symbol(Symbol {
                    name: self.abi_name(name),
                    value: offset,
                    size: data.len() as u64,
                    binding: scope_binding(d.get_scope()),
                    visibility: convert_visibility(d.get_visibility()),
                    kind: SymbolKind::Data,
                    section: Some(section_id),
                });
            }
            DefinedDecl::Section(_) => {}
        }
        self.symbols.insert(string_id, symbol_id);
    }

    fn import(&mut self, name: &str, kind: &ImportKind) {
        let string_id = self.strings.get_or_intern(&*name);
        let kind = match kind {
            ImportKind::Function => SymbolKind::Text,
            ImportKind::Data => SymbolKind::Data,
        };
        let symbol = Symbol {
            name: self.abi_name(name),
            value: 0,
            size: 0,
            binding: Binding::Global,
            visibility: Visibility::Default,
            kind,
            section: None,
        };
        let symbol_id = self.object.add_symbol(symbol);
        self.symbols.insert(string_id, symbol_id);
    }

    fn link(&mut self, l: &LinkAndDecl) {
        let to_symbol = {
            let to_idx = self.strings.get_or_intern(l.to.name);
            self.symbols.get(&to_idx).unwrap()
        };
        let (from_section, from_offset) = {
            let from_idx = self.strings.get_or_intern(l.from.name);
            self.sections.get(&from_idx).unwrap()
        };
        let mut subkind = RelocationSubkind::Default;
        let (kind, size, addend) = match l.reloc {
            Reloc::Auto => match *l.from.decl {
                Decl::Defined(DefinedDecl::Function { .. }) => match *l.to.decl {
                    Decl::Defined(DefinedDecl::Function { .. }) => {
                        subkind = RelocationSubkind::X86Branch;
                        (RelocationKind::Relative, 32, -4)
                    }
                    Decl::Import(ImportKind::Function) => {
                        subkind = RelocationSubkind::X86Branch;
                        (RelocationKind::PltRelative, 32, -4)
                    }
                    Decl::Defined(DefinedDecl::Data { .. }) => (RelocationKind::Relative, 32, -4),
                    Decl::Import(ImportKind::Data) => {
                        subkind = RelocationSubkind::X86RipRelativeMovq;
                        (RelocationKind::GotRelative, 32, -4)
                    }
                    _ => panic!("unsupported relocation {:?}", l),
                },
                Decl::Defined(DefinedDecl::Data { .. }) => (RelocationKind::Absolute, 64, 0),
                _ => panic!("unsupported relocation {:?}", l),
            },
            Reloc::Raw { reloc, addend } => (RelocationKind::Other(reloc), 0, addend),
            Reloc::Debug { size, addend } => (RelocationKind::Absolute, size * 8, addend),
        };
        let addend = i64::from(addend);
        let relocation = Relocation {
            offset: from_offset + l.at,
            symbol: *to_symbol,
            kind,
            subkind,
            size,
            addend,
        };
        self.object.sections[from_section.0]
            .relocations
            .push(relocation);
    }

    fn abi_name(&self, name: &str) -> Vec<u8> {
        let mut result = Vec::new();
        match self.object.format {
            BinaryFormat::Elf | BinaryFormat::Coff => {}
            BinaryFormat::Macho => result.push(b'_'),
            _ => unimplemented!(),
        }
        result.extend(name.as_bytes());
        result
    }
}

pub fn to_bytes(artifact: &Artifact, format: BinaryFormat) -> Vec<u8> {
    let mut state = State::new(artifact, format);
    state.object.add_symbol(Symbol {
        name: artifact.name.as_bytes().to_vec(),
        value: 0,
        size: 0,
        binding: Binding::Local,
        visibility: Visibility::Default,
        kind: SymbolKind::File,
        section: None,
    });
    for def in artifact.definitions() {
        state.definition(def.name, def.data, def.decl);
    }
    for (ref import, ref kind) in artifact.imports() {
        state.import(import, kind);
    }
    for link in artifact.links() {
        state.link(&link);
    }
    state.object.finalize();
    state.object.write()
}
