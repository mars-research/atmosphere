extern crate nasm_rs;

macro_rules! source {
    ($($arg:tt)*) => {
        println!("cargo:rerun-if-changed={}", format_args!($($arg)*));
    };
}

macro_rules! static_link {
    ($lib: expr) => {
        println!("cargo:rustc-link-lib=static={}", $lib);
    };
}

fn main() {
    println!("Baking garlic bread...");
    source!("build.rs");
    x86_64_asm("multiboot_header.asm");
    x86_64_asm("crt0.asm");
}

fn x86_64_asm(source: &str) {
    let arch_dir = "src/boot";
    source!("{}/{}", arch_dir, source);

    let mut mb = nasm_rs::Build::new();
    mb.file(&format!("{}/{}", arch_dir, source));
    mb.target("");
    mb.flag("-felf64");
    mb.compile(source);

    static_link!(source);
}
