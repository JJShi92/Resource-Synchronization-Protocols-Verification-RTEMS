# Frama-C installation

- If Frama-C 22 is provided by your distribution, try that. For a more flexible way with the possibility for newes packages if required, use Opam as described below.
  - Frama-C > 22 has been witnessed not to work with the presented setup of contracts, source code and command-line options. Further adaptions may be required to profit from newer Frama-C-versions' features.
- Install Opam, best with your distributions package manager
- For Opam commands, no root permissions are necessary if no system-wide installation of packages is required
- Initialize Opam with `opam init` and let it modify your .bash_profile
  - (for more info on opam, see [Opam Usage](https://opam.ocaml.org/doc/Usage.html))
- update the current shell as proposed with `eval $(opam env --switch=default)`
- install frama-c
  - `$ opam install frama-c.22.0`
  - this will download sources and automatically build packages. Install potentially needed system package dependencies as advised
- configure the provers:
  - `$ why3 config --detect`
- for me, frama-c was shipped with alt-ergo 2.4.1, which why3 didn't detect. If you encounter that too, downgrade with
  - `$ opam install alt-ergo.2.2.0`
- then run config detection again
- for more info on frama-c with opam, see [Frama-C Opam Install](https://git.frama-c.com/pub/frama-c/blob/master/INSTALL.md)

# Prerequisites

- RTEMS:
  - examples performed with [RTEMS 5.1](https://ftp.rtems.org/pub/rtems/releases/5/5.1/)
  - provide a cross-compilation toolchain
  - configure the source code
- provide "stubs" to be included
- provide annotated source code


# Frama-C: Usage

## Folder structure

```
${base}/
├── build
│   ├── ppc5.1
│   │   └── (...)
│   ├── ppc5.1_SC
│   │   └── (...)
├── src
|   ├── rtems-5.1
|   |   ├── cpukit
|   |   |   ├── fc_common_stubs.h
|   |   |   ├── fc_icpp_stubs.h
|   |   |   ├── fc_mrsp_stubs.h
|   |   |   └── include
|   |   |       └── rtems
|   |   |           └── score
|   |   |               ├── coremuteximpl.h
|   |   |               └── mrspimpl.h
|   |   └── (...)
```

## Command

- `${base}` is your starting point for your RTEMS sources and config directories. Please note that I didn't test the commands with this placeholder but used absolute paths instead.
- the command is to be run from the cpukit directory (`${base}/rtems-ppc/src/rtems-5.1/cpukit`) for correct resolution of relative paths
- Toolchain: `${base}/rtems-ppc/build/ppc5.1-tools`
- config directory for singlecore: `${base}/rtems-ppc/build/ppc5.1_SC`
- config directory for multicore (`RTEMS_SMP` defined): `${base}/rtems-ppc/build/ppc5.1`
- the stubs / function contracts are passed via the `-include fc_xyz_stubs.h` option within the cpp command
- the last argument is the target source file which contains the (annotated) functions to be analyzed

- Example Frama-C invocation with gui, using `fc_icpp_stubs.h` and targeting `coremuteximpl.h`
- for MrsP, exchange stub and implementation header and config directory

        $ frama-c-gui \
            -cpp-command '${base}/rtems-ppc/build/ppc5.1-tools/bin/powerpc-rtems5-gcc -C -E \
            -I./include -I./score/cpu/powerpc/include/ \
            -I../../../build/ppc5.1_SC/powerpc-rtems5/c/qemuppc/include/ \
            -I${base}/rtems-ppc/build/ppc5.1-tools/powerpc-rtems5/include \
            -I${base}/rtems-ppc/build/ppc5.1-tools/lib/gcc/powerpc-rtems5/7.5.0/include \
            -nostdinc -include fc_icpp_stubs.h' -machdep ppc_32 -cpp-frama-c-compliant -c11 \
            include/rtems/score/coremuteximpl.h

- starting from the verification target, frama-c resolves the dependencies and hence parses a lot of code
- in the left of the GUI, find the verification target and inspect the annotated functions. Contracts are 'rendered' and the C-code is displayed in the intermediate normalized form
- select a single proof goal or right-click the function name to prove all targets with WP. Occasionally, a second pass is required.
- below the source code view, you can see details on the proofs under the tab 'WP Goals'
- on the left below the function list, WP's parameters such as timeouts can be configured
  - All config options are accessible via Analyses->Analyses. Options highlighted blue differ from the defaults. You will find every option passed via the command-line represented (and editable) here.
- In the top toolbar you can reparse the loaded sources which is handy if you change annotations or stub headers. However, sometimes a reload fails for some reason and only closing / relaunching the application with the above command works
- Please also refer to the very helpful [docs on Frama-C and WP](https://frama-c.com/fc-versions/titanium.html) and the [Tutorials](https://frama-c.com/html/tutorials.html)

## Non-Interactive with CLI

- use `frama-c` instead of `frama-c-gui`
- set verification targets with -wp-fct, e.g. `-wp-fct _CORE_ceiling_mutex_Set_owner,_CORE_ceiling_mutex_Seize,_CORE_ceiling_mutex_Surrender` for ICPP



# Appendix

- fc_common_stubs.h, fc_icpp_stubs.h, fc_mrsp_stubs.h: headers with annotated system functions
- coremuteximpl-stripped.h, mrspimpl-stripped.h: function contracts for ICPP and MrsP, extracted from implementation headers
- coremuteximpl.h, mrspimpl.h: implementation headers containing ICPP/MrsP function contracts and the proposed ICPP fix (verification target)
- init.c: RTEMS Test for ICPP's priority ceiling check (for an explanation see thesis/Listing B.0.1)

