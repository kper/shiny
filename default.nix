{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  name = "shiny-shell";
  buildInputs = [
  ];
  shellHook = ''
    export EDITOR='vim'
  '';
}
