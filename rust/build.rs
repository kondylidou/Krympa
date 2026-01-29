use std::{fs, path::Path, process::Command};

fn main() {
    let ocaml_dir = "../ocaml";

    println!("Building OCaml project in {}", ocaml_dir);

    // Build the OCaml project with dune
    let status = Command::new("dune")
        .arg("build")
        .current_dir(ocaml_dir)
        .status()
        .expect("Failed to run dune build");
    if !status.success() {
        panic!("dune build failed");
    }

    // Path to built executable
    let built_path = format!("{}/_build/default/bin/main.exe", ocaml_dir);
    let dest_dir = "../rust/ocaml_install";
    let dest_path = format!("{}/tptp_parser", dest_dir);

    println!("Looking for OCaml executable at: {}", built_path);
    println!("Destination directory: {}", dest_dir);

    // Create destination directory if needed
    fs::create_dir_all(dest_dir).expect("Failed to create destination directory");

    // Remove existing file if it exists to avoid permission errors
    if Path::new(&dest_path).exists() {
        println!("Removing existing executable at {}", dest_path);
        fs::remove_file(&dest_path).expect("Failed to remove old OCaml executable");
    }

    // Copy the executable
    fs::copy(&built_path, &dest_path).expect(&format!(
        "Failed to copy OCaml executable from {}",
        built_path
    ));

    println!("cargo:rerun-if-changed={}/lib", ocaml_dir);
}
