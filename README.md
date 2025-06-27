# AsymptoticPLP




## Description
AsymptoticPLP implements several independently useful steps, namely converting between logic programs and explicit least fixed point functions, and determining the asymptotically equivalent quantifier-free formula corresponding to a least fixed point function on a large random structure. 

It then combines these to a static analysis tool for probabilistic logic programs, computing to any proabilistic logic program a determinate program asymptotically equivalent to it on large domains. This can be used quickly to gauge the implications of probabilistic modelling choices for transfer across differently sized domains. 

More information can be found in the thesis and paper contained in the docs folder.

## Installation
AsymptoticPLP is intended to be run under SWI-Prolog and has been tested with versions 8 and 9. No other Prolog distribution has been tested, and it is not expected to work under other distributions due to the use of SWI-Prolog specific libraries.  

## Authors and acknowledgment
The initial version of AsymptoticPLP was developed by Bao Loi Quach during her Master thesis research at the LMU in 2020-2022. It has been updated and is currently maintained by Felix Weitkämper. 
## License

Still open. Maybe Artistic License 2.0 is reasonable, as it would allow for having a single license also for projects that incorporate code from Riguzzi's cplint suite?? Otherwise one could go for an MIT X11 license. 

## Project status
In alpha development, intended for some form of public release (possibly as part of the C-ProbLog project, or the PLP-BN tools) in 2025.
