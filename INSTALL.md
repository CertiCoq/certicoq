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


## Via opam (preferred)

First, pin the dependencies:

```console
$ opam pin -n -y submodules/coq-ext-lib
$ opam pin -n -y submodules/Equations
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

## Manual

Make sure that you do not have any of the dependencies installed already. From the `certicoq/` directory, run:

```console
$ make submodules
```
    
Note that this approach will only work if your installation path for Coq is writable  without root privileges.

### Building the compiler

From the `certicoq/` directory, run:

```console
$ make -j4
```

After the sources are successfully compiled, you can compile and install the CertiCoq plugin with:

```console
# make install
```

To test the installation, you can go to `certicoq/benchmarks` and run

```console
$ make all
```
