#![deny(unused_must_use)]

extern crate nasm_rs;

use std::path::{Path, PathBuf};
use std::process::Command;

macro_rules! source {
    ($($arg:tt)*) => {
        println!("cargo:rerun-if-changed={}", format_args!($($arg)*));
    };
}

fn main() {
    source!("build.rs");
    x86_64_asm_elf("dom1.asm");
}

fn x86_64_asm_elf(source: &str) {
    let path = Path::new("src/").join(source);
    source!("{}", path.to_str().unwrap());

    let objects = build_x86_64_asm(&path);
    for object in objects {
        let out_dir = object.parent().expect("Must have a parent");

        let object_stem = object
            .file_stem()
            .expect("Must be a file, not a directory")
            .to_str()
            .expect("Must be UTF-8");
        let linked_name = format!("{}.elf", object_stem);

        let linked = out_dir.join(linked_name);

        // .o -> static-pie elf
        let ld = Command::new("x86_64.ld")
            .args(&["--pie", "--no-dynamic-linker"])
            .arg("-o")
            .arg(&linked)
            .arg(&object)
            .status()
            .expect("Failed to spawn x86_64.ld");

        if !ld.success() {
            panic!("ld failed");
        }

        //panic!("SUCCESS: {:?}", linked);
    }
}

fn build_x86_64_asm(source: &Path) -> Vec<PathBuf> {
    let mut mb = nasm_rs::Build::new();
    mb.file(source);
    mb.target("");
    mb.flag("-felf64");

    mb.compile_objects().unwrap()
}
