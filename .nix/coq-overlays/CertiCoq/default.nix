{
  lib,
  pkgs,
  mkCoqDerivation,
  coq,
  wasmcert,
  coqprime,
  compcert,
  metacoq,
  ExtLib,
  version ? null,
}:

with lib;
mkCoqDerivation {
  pname = "CertiCoq";
  mlPlugin = true;

  inherit version;
  releaseRev = v: "v${v}";

  buildInputs = [
    pkgs.clang
  ];

  propagatedBuildInputs = [
    wasmcert # TODO: enforce 2.2.0
    coqprime
    compcert
    ExtLib
    metacoq # TODO: enforce 1.3.1+8.20
  ];

  patchPhase = ''
    patchShebangs ./configure.sh
    patchShebangs ./clean_extraction.sh
    patchShebangs ./make_plugin.sh
  '';

  configurePhase = ''
    ./configure.sh local
  '';

  buildPhase = ''
    runHook preBuild

    make
    make plugin
    make cplugin

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    OUTDIR=$out/lib/coq/${coq.coq-version}/user-contrib

    DST=$OUTDIR/CertiCoq/Plugin/runtime make -C runtime install
    COQLIBINSTALL=$OUTDIR make -C theories install
    COQLIBINSTALL=$OUTDIR make -C libraries install
    COQLIBINSTALL=$OUTDIR COQPLUGININSTALL=$OCAMLFIND_DESTDIR make -C plugin install
    COQLIBINSTALL=$OUTDIR COQPLUGININSTALL=$OCAMLFIND_DESTDIR make -C cplugin install

    runHook postInstall
  '';

  meta = {
    description = "CertiCoq";
    maintainers = with maintainers; [ womeier ];
    license = licenses.mit;
  };
}
