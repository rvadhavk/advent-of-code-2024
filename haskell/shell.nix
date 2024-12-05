{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = [
    pkgs.haskell.compiler.ghc98
    pkgs.cabal-install
  ];
}
