{ pkgs ? import ((import <nixpkgs> { }).fetchFromGitHub {
  owner = "nixos";
  repo = "nixpkgs";
  rev = "23.11";
  hash = "sha256-MxCVrXY6v4QmfTwIysjjaX0XUhqBbxTWWB4HXtDYsdk=";
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
    ];
}
