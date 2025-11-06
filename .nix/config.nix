{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/rocq-overlays`
  ## and `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "CertiCoq";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  default-bundle = "default";
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  bundles.default = {
    ## You can override Rocq and other Rocq rocqPackages
    ## through the following attribute
    # rocqPackages.rocq-core.override.version = "9.0";

    ## You can override Coq and other Coq coqPackages
    ## through the following attribute
    coqPackages.coq.override.version = "8.20";
    coqPackages.compcert.override.version = "3.14";
    coqPackages.wasmcert.override.version = "v2.2.0";

    ## In some cases, light overrides are not available/enough
    ## in which case you can use either
    # rocqPackages.<rocq-pkg>.overrideAttrs = o: <overrides>;
    # coqPackages.<coq-pkg>.overrideAttrs = o: <overrides>;
    ## or a "long" overlay to put in `.nix/rocq-overlays` or `.nix/coq-overlays`
    ## you may use `nix-shell --run fetchOverlay <coq-pkg>`
    ## to automatically retrieve the one from nixpkgs
    ## if it exists and is correctly named/located

    ## You can override Coq and other coqPackages
    ## through the following attribute
    ## If <ocaml-pkg> does not support light overrides,
    ## you may use `overrideAttrs` or long overlays
    ## located in `.nix/ocaml-overlays`
    ## (there is no automation for this one)
    #  ocamlPackages.<ocaml-pkg>.override.version = "x.xx";

    ## You can also override packages from the nixpkgs toplevel
    # <nix-pkg>.override.overrideAttrs = o: <overrides>;
    ## Or put an overlay in `.nix/overlays`

    ## you may mark a package as a main CI job (one to take deps and
    ## rev deps from) as follows
    # coqPackages.<main-pkg>.main-job = true;
    ## by default the current package and its shell attributes are main jobs

    ## you may mark a package as a CI job as follows
    #  rocqPackages.<another-pkg>.job = "test";
    #  coqPackages.<another-pkg>.job = "test";
    ## It can then built through
    ## nix-build --argstr bundle "default" --arg job "test";
    ## in the absence of such a directive, the job "another-pkg" will
    ## is still available, but will be automatically included in the CI
    ## via the command genNixActions only if it is a dependency or a
    ## reverse dependency of a job flagged as "main-job" (see above).

    ## Run on push on following branches (default [ "master" ])
    # push-branches = [ "master" "branch2" ];
  };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community = { };
}
