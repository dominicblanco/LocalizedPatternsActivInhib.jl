# Computer-assisted proofs of localized patterns and saddle node bifurcations in 1D Activator-Inhibitor models.



Table of contents:


* [Introduction](#introduction)
* [Activator-Inhibitor Models](#activator-inhibitor-models)
   * [Proof of the patterns](#proof-of-the-patterns)
   * [Proof of the saddle node](#proof-of-the-saddle-node)
   * [Stability analysis](#stability-analysis)
* [Utilisation and References](#utilisation-and-references)
* [License and Citation](#license-and-citation)
* [Contact](#contact)



# Introduction

This Julia code is a complement to the article 

#### [[1]](To appear) : "Proving the existence of localized patterns and saddle node bifurcations in 1D activiator-inhibitor type models", D. Blanco, M. Cadiot, and D. Fassler, [ArXiv Link](To appear).

It provides the necessary rigorous computations of the bounds presented along the paper. The computations are performed using the package [IntervalArithmetic](https://github.com/JuliaIntervals/IntervalArithmetic.jl). The mathematical objects (spaces, sequences, operators,...) are built using the package [RadiiPolynomial](https://github.com/OlivierHnt/RadiiPolynomial.jl). Detailed instructions are available in the code to help the user run it.


# Activator-Inhibitor Models

The class of Activator-Inhibitor models we consider are of the following form
$$0 = \delta^2 \Delta u - cu + dv + u^2v + a$$
$$ 0 = \Delta v + hu - jv - u^2v + b$$
is known to have localized solutions on $\mathbb{R}$ that vanish at infinity as demonstrated in [[1]](https://academic.oup.com/imamat/article/86/5/1031/6352382). These solutions are called localized patterns (see [[1]](https://arxiv.org/abs/2302.12877) for an introduction to the subject). The theory needed to prove these patterns was demonstrated in [[1]](https://arxiv.org/abs/2403.10450)

## Proof of the patterns

A candidate solution for the proof of the patterns are provided in the files UV_Glycolsis, UV_Brusselator, UV_Brusselator_Multipulse, UV_Schnakenberg, UV_RootHair, and UV_SelkovSchnakenberg. These correspond to the sequence $\overline{U}$ in Section 3.2 representing the approximate solution $\overline{u}$. In particular, we provide the needed code to project $\overline{U}$ in the set of sequences representing trace zero functions. Consequently, the Fourier series associated to \overline{U}$ represents a smooth function on $\mathbb{R}$ with compact support on a square $\Omega_0$. In the scalar case, the approximate solution is computed in the code using a Newton method.

Given these approximate solutions, the code LocalizedPatternsActivInhib.jl provides the explicit computation of the bounds presented in Section 4. It also provides a value for $r_0$ where the proof is successful. One can comment and uncomment the necessary part to prove the solution they wish.

## Proof of the saddle node

Similar to the patterns, a candidate solution for the proof of the saddle node is provided in the file X_saddle. This corresponds to the sequence $\overline{X}$ described in Section 5 representing the approximate solution $\overline{x}$. We build $\overline{u}$ as previously, compute an approximation of the eigenvectors denoted $\overline{W}$ and eigenvalue denoted $\overline{\nu}$. We then ensure $\overline{W}$ represents a smooth function on $\mathbb{R}$ with compact support on a square $\Omega_0$ as we did for $\overline{U}$. This leads to the definition of $\overline{X} = (\overline{\nu},\overline{U},\overline{W})$ and then $\overline{x} = (\overline{\nu},\overline{u},\overline{w})$. 

Given this approximate solution, the code SaddleNodeMapActivInhib.jl provides the explicit computation of the bounds presented in Section 5. It also provides a value for $r_0$ where the proof is successful. 

## Stability Analysis

In the previous part, we proved a zero of the saddle node map introduced in Section 5. In order to ensure we have proven a saddle node bifurcation, we need to rule out a degenerate Hopf bifurcation. This can be done by proving the stability of the solution. We provide the necessary code at the conclusion of the code SaddleNodeMapActivInhib.jl in order to prove the result of Thoerem 6.6. This ensures we have a saddle node bifurcation.

Additionally, we prove the stability of the solutions to Glycolsis and Root-Hair, which are given in the files UV_Glycolsis and UV_RootHair. This proves the results of Thoerems 6.7 and 6.8. The stability analysis is performed automatically when running the code LocalizedPatternsActivInhib.jl, so one could attempt to prove the stability of the other candidate solutions as well.
 
 # Utilisation and References

 The codes in LocalizedPatternsActivInhib.jl and SaddleNodeMapActivInhib.jl can serve to prove other patterns than the ones provided as illustration should one have the numerical candidates. In particular, the projection in the set of functions with null trace of order $2$ is computed in the code, meaning one can just provide the numerical candidate and attempt a proof.
 
 The code is build using the following packages :
 - [RadiiPolynomial](https://github.com/OlivierHnt/RadiiPolynomial.jl) 
 - [IntervalArithmetic](https://github.com/JuliaIntervals/IntervalArithmetic.jl)
 - [LinearAlgebra](https://docs.julialang.org/en/v1/stdlib/LinearAlgebra/)
 - [JLD2](https://github.com/JuliaIO/JLD2.jl)
 
 
 # License and Citation
 
This code is available as open source under the terms of the [MIT License](http://opensource.org/licenses/MIT).
  
If you wish to use this code in your publication, research, teaching, or other activities, please cite it using the following BibTeX template:

```
@software{LocalizedPatternsActivInhib.jl,
  author = {Dominic Blanco, Matthieu Cadiot, and Daniel Fassler},
  title  = {LocalizedPatternsActivInhib.jl},
  url    = {https://github.com/dominicblanco/LocalizedPatternsActivInhib.jl},
  note = {\url{ https://github.com/dominicblanco/LocalizedPatternsActivInhib.jl},
  year   = {2025},
  doi = {10.5281/zenodo.17170735}
}}
```
DOI : [10.5281/zenodo](https://doi.org/10.5281/zenodo.17170735) 


# Contact

You can contact us at :

dominic.blanco@mail.mcgill.ca
matthieu.cadiot@polytechnique.edu
daniel.fassler@mail.concordia.ca