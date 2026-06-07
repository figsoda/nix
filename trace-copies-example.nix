# NIX_TRACE_COPIES=1 nix run . -- eval -f trace-copies-example.nix --raw

let
  show = label: path: "${label}: ${path}";

  pkgs = import <nixpkgs> { };

  doc = ./doc;
  manual = doc + "/manual";
in
''
  ${show "readme" ./README.md}
  ${show "manual" manual}
  ${show "pkgs.path" pkgs.path}
  ${show "stdenv" pkgs.stdenv}
''
