{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  attribute = "CakeMLExtraction";

  no-rocq-yet = true;

  default-bundle = "9.1";

  bundles."9.1" = {
    coqPackages = {
      coq.override.version = "9.1";
      # the MetaRocq 9.1 snapshot that Peregrine pins (rocq-peregrine.opam)
      metarocq-utils.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-common.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-template-rocq.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-pcuic.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-safechecker.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-safechecker-plugin.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-template-pcuic.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-erasure.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      metarocq-erasure-plugin.override.version = "51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56";
      ceres-bs.override.version = "1.0.0";
    }; rocqPackages = {
      rocq-core.override.version = "9.1";
    };
    push-branches = [ "main" "rocq-9.1" ];
  };



  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  cachix.metarocq = {};
  cachix.peregrine.authToken = "CACHIX_AUTH_TOKEN";
}
