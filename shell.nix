{ pkgs ? import (builtins.fetchGit {
  url = "https://github.com/nixos/nixpkgs/";
  ref = "refs/tags/23.11";
}) {} }:
let
  haskellPackages = pkgs.haskell.packages.ghc96.override
    {
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
    pkgs.nil
    (pkgs.writeShellScriptBin
      "build"
      "${unlit}/bin/unlit --to=backtickfence --language=haskell --input=existentials-on-a-leash.lhs | ${pkgs.gnused}/bin/sed 's/^\\\\#/#/' > existentials-on-a-leash.md")
  ];
}
