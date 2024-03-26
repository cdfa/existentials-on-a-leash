{ pkgs ? import <nixpkgs> { } }:
let
  all-cabal-hashes = pkgs.fetchurl {
    url = "https://github.com/commercialhaskell/all-cabal-hashes/archive/d77837f979c4b15fe0eb25cdf8a0463773434c9d.tar.gz";
    sha256 = "sha256-dRJw1rA5hZHZ5ftxe+G2YekiYwqUxUIphxiDy23YMAY=";
  };
  haskellPackages = pkgs.haskell.packages.ghc96.override
    {
      # inherit all-cabal-hashes;
      overrides = self: super:
        {
          equational-reasoning = self.callCabal2nix "equational-reasoning"
            (builtins.fetchTarball {
              url = "https://hackage.haskell.org/package/equational-reasoning-0.7.0.2/equational-reasoning-0.7.0.2.tar.gz";
            })
            { };
          linear-generics = self.callCabal2nix "linear-generics"
            (builtins.fetchTarball {
              url = "https://hackage.haskell.org/package/linear-generics-0.2.3/linear-generics-0.2.3.tar.gz";
            })
            { };
        };
    };
in
pkgs.mkShell
{
  buildInputs = with haskellPackages; [
    (ghcWithPackages
      (p: with p; [
        linear-base
        lens
        sized
        ghc-typelits-presburger
        ghc-typelits-knownnat
      ]))
    apply-refact
    fourmolu

    hlint
    ghcid
    haskell-language-server

    pkgs.cabal-install
    pkgs.rnix-lsp
    (pkgs.writeShellScriptBin
      "build"
      "${unlit}/bin/unlit --to=backtickfence --language=haskell --input=existentials-on-a-leash.lhs | ${pkgs.gnused}/bin/sed 's/^\\\\#/#/' > existentials-on-a-leash.md")
  ];
}
