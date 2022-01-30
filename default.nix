with (import <nixpkgs> {});

mkShell {
  name = "shiny-shell";
  buildInputs = [
	wabt
  ];
  shellHook = ''
    export EDITOR='vim'
  '';
}
