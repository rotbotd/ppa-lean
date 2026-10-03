{
  description = "A chapter-by-chapter, tacticless Lean formalization of Principles of Program Analysis";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.transport-span = {
    url = "github:rotbotd/lean-transport-span/c415425";
    flake = false;
  };

  outputs = { self, nixpkgs, transport-span }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      devShells.${system}.default = pkgs.mkShell {
        packages = [ pkgs.lean4 ];
      };

      packages.${system}.default = pkgs.stdenvNoCC.mkDerivation {
        pname = "ppa-lean";
        version = "0.1.0";
        src = self;
        nativeBuildInputs = [ pkgs.lean4 ];
        buildPhase = ''
          export HOME="$TMPDIR/home"
          mkdir -p "$HOME"
          mkdir -p .lake/packages
          cp -R ${transport-span} .lake/packages/transport-span
          chmod -R u+w .lake/packages/transport-span
          substituteInPlace lakefile.toml \
            --replace-fail \
              'git = "https://github.com/rotbotd/lean-transport-span"' \
              'path = ".lake/packages/transport-span"' \
            --replace-fail 'rev = "c415425"' '# revision supplied by flake.lock'
          rm lake-manifest.json
          lake update
          lake build
        '';
        installPhase = ''
          mkdir -p "$out"
          cp -r .lake/build/lib "$out/lib"
        '';
      };

      checks.${system}.default = self.packages.${system}.default;
    };
}
