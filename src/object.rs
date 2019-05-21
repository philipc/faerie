use crate::artifact::{
    self, Artifact, DataType, Decl, DefinedDecl, ImportKind, LinkAndDecl, Reloc, Scope,
};
use object_write::{
    Binding, Object, Relocation, RelocationKind, Section, SectionId, SectionKind,
    Symbol, SymbolId, SymbolKind, Visibility,
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
    sections: HashMap<StringIndex, SectionId>,
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
        let section = match decl {
            DefinedDecl::Function(d) => {
                let kind = SectionKind::Text;
                let name = self.object.section_name(kind, name.as_bytes());
                let align = d.get_align().unwrap_or(16) as u64;
                Section::new(name, kind, data.to_vec(), align)
            }
            DefinedDecl::Data(d) => {
                let kind = match d.get_datatype() {
                    DataType::Bytes => {
                        if d.is_writable() {
                            SectionKind::Data
                        } else {
                            SectionKind::ReadOnlyData
                        }
                    }
                    DataType::String => SectionKind::ReadOnlyString,
                };
                let name = self.object.section_name(kind, name.as_bytes());
                let align = d.get_align().unwrap_or(1) as u64;
                Section::new(name, kind, data.to_vec(), align)
            }
            DefinedDecl::Section(d) => {
                // TODO: this behavior should be deprecated, but we need to warn users!
                let kind = if name == ".debug_str" || name == ".debug_line_str" {
                    SectionKind::OtherString
                } else {
                    match d.get_datatype() {
                        DataType::Bytes => SectionKind::Other,
                        DataType::String => SectionKind::OtherString,
                    }
                };
                let name = name.as_bytes().to_vec();
                let align = d.get_align().unwrap_or(1) as u64;
                Section::new(name, kind, data.to_vec(), align)
            }
        };
        let section_id = self.object.add_section(section);
        self.sections.insert(string_id, section_id);

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
                    name: name.as_bytes().to_vec(),
                    value: 0,
                    size: data.len() as u64,
                    binding: scope_binding(d.get_scope()),
                    visibility: convert_visibility(d.get_visibility()),
                    kind: SymbolKind::Text,
                    section: Some(section_id),
                });
            }
            DefinedDecl::Data(d) => {
                symbol_id = self.object.add_symbol(Symbol {
                    name: name.as_bytes().to_vec(),
                    value: 0,
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
            name: name.as_bytes().to_vec(),
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
        let from_section = {
            let from_idx = self.strings.get_or_intern(l.from.name);
            self.sections.get(&from_idx).unwrap()
        };
        let (kind, size, addend) = match l.reloc {
            Reloc::Auto => match *l.from.decl {
                Decl::Defined(DefinedDecl::Function { .. }) => match *l.to.decl {
                    Decl::Defined(DefinedDecl::Function { .. }) => {
                        (RelocationKind::Relative, 32, -4)
                    }
                    Decl::Import(ImportKind::Function) => (RelocationKind::PltRelative, 32, -4),
                    Decl::Defined(DefinedDecl::Data { .. }) => (RelocationKind::Relative, 32, -4),
                    Decl::Import(ImportKind::Data) => (RelocationKind::GotRelative, 32, -4),
                    _ => panic!("unsupported relocation {:?}", l),
                },
                Decl::Defined(DefinedDecl::Data { .. }) => (
                    RelocationKind::Absolute,
                    self.object.architecture.pointer_width().unwrap().bits(),
                    0,
                ),
                _ => panic!("unsupported relocation {:?}", l),
            },
            Reloc::Raw { reloc, addend } => (RelocationKind::Other(reloc), 0, addend),
            Reloc::Debug { size, addend } => (RelocationKind::Absolute, size * 8, addend),
        };
        let addend = i64::from(addend);
        let relocation = Relocation {
            offset: l.at,
            symbol: *to_symbol,
            kind,
            size,
            addend,
        };
        self.object.sections[from_section.0]
            .relocations
            .push(relocation);
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
