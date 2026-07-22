# NIX_TRACE_IFD=1 nix run . -- eval -f trace-ifd-example.nix --raw

let
  show = label: value: "${label}: ${value}";

  pkgs = import <nixpkgs> { };

  generated = pkgs.runCommand "generated.nix" { } ''
    echo '{ greeting = "hello"; }' > $out
  '';

  message = pkgs.writeText "message" "hello from readFile";
in
''
  ${show "greeting" (import generated).greeting}
  ${show "message" (builtins.readFile message)}
''
