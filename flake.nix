{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = inputs:
    with inputs; let
      pkgs = import nixpkgs {
        system = "x86_64-linux";
        overlays = [(import rust-overlay)];
      };
      toolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchains.toml;
    in {
      devShells.x86_64-linux.default = pkgs.mkShell {
        packages = with pkgs; [
          toolchain
          cargo
          rust-analyzer
          rustfmt
          nil
        ];
      };
    };
}
