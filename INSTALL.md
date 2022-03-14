# Installing CertiCoq

## Get the code

Fetch the code:

```console
$ git clone git@github.com:CertiCoq/certicoq.git
```

Fetch the dependencies:

```console
$ git submodule update --init
```


## Install using opam (preferred)

First, pin the dependencies:

```console
$ opam pin -n -y submodules/metacoq
```

Next, pin CertiCoq:

```console
$ opam pin -n -y .
```

You can now install CertiCoq:

```console
$ opam install coq-certicoq
```

Alternatively, if you only want to install the dependencies, you can run:

```console
$ opam install coq-certicoq --deps-only
```

## Build & install manually

### Dependencies

If possible, install the dependencies using the opam instructions given above.

If that is not an option, you can instead use these "manual" instructions. Note that this approach will only work *if* your installation path for Coq is writable without root privileges.

Make sure that you do not have any of the dependencies installed already. From the `certicoq/` directory, run:

```console
$ make submodules
```


### Building the compiler

Once the dependencies are installed (either via opam or by the manual method), you can build the Coq theory by running

```console
$ make all
```

The plugin, which depends on the Coq theory, can be built by running

```console
$ make plugin
```

To install the theory & plugin, simply run

```console
$ make install
```


## Testing the installation

You can test the installation using the including benchmark suite:

```console
$ make -C benchmarks all
```
