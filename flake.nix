{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    rust-overlay.url = "github:oxalica/rust-overlay";
    crane.url = "github:ipetkov/crane";
  };

  outputs = inputs:
    with inputs; let
      pkgs = import nixpkgs {
        system = "x86_64-linux";
        overlays = [(import rust-overlay)];
        config.allowUnfreePredicate = pkg:
          builtins.elem (nixpkgs.lib.getName pkg) [
            "github-copilot-cli"
            "claude-code"
          ];
      };
      toolchain = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchains.toml;
      craneLib = crane.mkLib pkgs;
    in {
      packages.x86_64-linux.default = (craneLib.overrideToolchain toolchain).buildPackage {
        src = ./.;
        doCheck = false;
      };
      devShells.x86_64-linux.default = pkgs.mkShell {
        packages = with pkgs; [
          toolchain
          cargo
          cargo-insta
          rust-analyzer
          rustfmt
          nil
          bash
          github-copilot-cli
          opencode
          claude-code
          nodejs
        ];
      };
    };
}
