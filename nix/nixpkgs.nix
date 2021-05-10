let
  sources = import ./sources.nix;

  # Change to update toolchain version.
  rustNightly = "2021-05-05";
in import sources.nixpkgs {
  overlays = [
    (import sources.rust-overlay)
    (self: super: {
      rust-pinned = super.rust-bin.nightly.${rustNightly}.rust.override {
        extensions = [ "rust-src" ];
      };
    })
  ];
}
