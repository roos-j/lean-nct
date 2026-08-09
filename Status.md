# Formalization status

Definitions use `Todo` or `Completed`.  Theorems use exactly `Todo`,
`Statement completed`, or `Proof completed`; the last status means that the
proof is sorry-free and depends only on standard axioms.

## Introduction

### Twisted averages

#### Definitions

- [A_def]: [Completed] (Lean: twistedAverage, twistedAverageAtScale)

#### Theorems

- [thm:nct main real]: [Statement completed] (Lean: mainTwistedTheorem)

## Preliminaries

### Notation

#### Definitions

- [closed ball]: [Completed] (Lean: Metric.closedBall)
- [gaussian]: [Completed] (Lean: Notation.gaussian)
- [bracket bump]: [Completed] (Lean: Notation.bracketBump, Notation.scaledBracketBump, Notation.scaledBracketBumpReal)

### The Wiener space $W_0$

#### Definitions

#### Theorems

- [W_0 radius independence]: [Proof completed] (Lean: wienerNorm_le_max_one_three_mul_div_pow_mul, memW0_iff_integrable_wienerEnvelope)
- [P:lp-embedding]: [Proof completed] (Lean: MemW0.memLp)
- [W_0 fiber integrals]: [Proof completed] (Lean: exists_wienerEnvelope_fiber_and_integral_comp_injective_continuousLinearMap_bound)
- [tensor Wiener]: [Proof completed] (Lean: MemW0.fintype_tensor, fintype_tensor_wienerNorm_le)
- [W_0 Brascamp Lieb]: [Proof completed] (Lean: exists_brascamp_lieb_memW0)
- [P:schwartz-into-wiener]: [Proof completed] (Lean: SchwartzMap.memW0)
- [convolution vector]: [Proof completed] (Lean: memW0_convolutionAlongVector, fourier_convolutionAlongVector)

### $K$ kernels

#### Definitions

- [normalized function tuples]: [Completed] (Lean: normalizedFunctionTuples)
- [cube Brascamp--Lieb]: [Completed] (Lean: cubeBrascampLiebForm)
- [prism Brascamp--Lieb]: [Completed] (Lean: prismBrascampLiebForm)

#### Theorems

- [cube BL inequality]: [Proof completed] (Lean: cubeBLInequality)
- [prism BL inequality]: [Proof completed] (Lean: prismBLInequality)
- [simplification 1 prism]: [Proof completed] (Lean: simplificationOnePrism)
- [single cancellative Cauchy-Schwarz]: [Proof completed] (Lean: singlyCancellativeKernel_memW0, singlyCancellativeLift_memW0, singlyCancellativeCauchySchwarz_bound)
- [doubly cancellative Cauchy-Schwarz]: [Proof completed] (Lean: doublyCancellativeKernel_memW0, doublyCancellativeLift_memW0, doublyCancellativeCauchySchwarz_bound)
- [Positivity K]: [Proof completed] (Lean: positivityKernel_memW0, positivityKernel_nonnegative)
- [Monotonicity K]: [Proof completed] (Lean: monotonicityK)

### $M$ kernels

#### Definitions


#### Theorems

- [M to K]: [Proof completed] (Lean: mToK, mToK_integrand_memW0, mToK_memW0, mToK_eLpNorm_one_le)
- [Positivity M]: [Proof completed] (Lean: positivityM_memW0, positivityM_nonnegative)
- [Cauchy-Schwarz at k]: [Proof completed] (Lean: cauchySchwarzKernel_memW0, cauchySchwarzLift_memW0, cauchySchwarzAtK_bound)
- [Cauchy-Schwarz at n-1]: [Proof completed] (Lean: doublyCauchySchwarzKernel_memW0, cauchySchwarzLift_memW0, cauchySchwarzAtNMinusOne_bound, cauchySchwarzAtNMinusOne)

### Multiplicatively spaced monotone sequences

#### Definitions

- [multiplicatively spaced monotone sequences]: [Completed] (Lean: SpacedSequence, A)
- [Distance of spaced sequences]: [Completed] (Lean: WithinSequenceDistance, SequenceDistance)
- [closed balls in A]: [Completed] (Lean: sequenceDistanceBall)

#### Theorems

- [Extension of sequences]: [Proof completed] (Lean: extensionOfSequences)
- [Operations on spaced sequences]: [Proof completed] (Lean: max_mem_A, smul_mem_A, shift_mem_A, sqrt_sq_add_sq_mem_A)
- [Properties of distance of sequences]: [Proof completed] (Lean: sequenceDistance_zero_eq, sequenceDistance_comm, sequenceDistance_triangle, sequenceDistance_shift_le, sequenceDistance_smul, sequenceDistance_pow_two_smul_le)

### Gaussians

#### Definitions

#### Theorems

- [square root one minus Gaussian]: [Proof completed] (Lean: sqrtOneMinusGaussian, continuous_sqrtOneMinusGaussian, sqrtOneMinusGaussian_lower, sqrtOneMinusGaussian_bounds)
- [Gaussian bump decay]: [Todo] (Lean: gaussianBumpDecay)
- [Elementary Gaussian properties]: [Todo] (Lean: gaussian_memW0, gaussian_fourier_fixed, gaussianRescale_convolution, gaussianRescale_fourier)
- [poisson to abel]: [Proof completed] (Lean: poissonKernel, poissonKernel_fourier)
- [auxiliary function B]: [Proof completed] (Lean: auxiliaryFunctionB_properties)
- [square root of Gaussian decay]: [Todo] (Lean: sqrtGaussianDecay)

### Bumps and their estimates

#### Definitions

- [standard bump]: [Completed] (Lean: standardBumpFinite, standardBump, standardBumpRescale)

#### Theorems

- [lem:smoothdecay]: [Todo] (Lean: smoothDecay)
- [lem: min and bracket]: [Proof completed] (Lean: min_and_bracket)
- [lem:smoothdecay2]: [Todo] (Lean: smoothDecay2)
- [mean value bump estimate 2]: [Todo] (Lean: meanValueBumpEstimate)
- [standard bump properties]: [Todo] (Lean: standardBumpProperties)
- [compare brackets]: [Proof completed] (Lean: compare_brackets)
- [two bump estimate]: [Todo] (Lean: twoBumpEstimate)
- [orthogonal domination]: [Todo] (Lean: orthogonalDomination)
- [orthogonal decay]: [Todo] (Lean: orthogonalDecay)
- [bump triangle]: [Proof completed] (Lean: bump_triangle)
- [Gaussian domination]: [Todo] (Lean: gaussianDomination)
- [diagonal square root]: [Todo] (Lean: diagonalSquareRoot)
- [derivative of diagonal square root]: [Todo] (Lean: derivativeDiagonalSquareRoot)
- [L:gaussian-estimate]: [Todo] (Lean: gaussianEstimate)
- [L:gaussian-bump-estimate]: [Todo] (Lean: gaussianBumpEstimate)
- [L:derivative-estimate-for-G]: [Todo] (Lean: derivativeEstimateForG)
- [L:faa-di-bruno]: [Todo] (Lean: faaDiBruno)
- [L:second-gaussian-estimate]: [Todo] (Lean: secondGaussianEstimate)
- [L:gaussian-bump-decomposition]: [Todo] (Lean: gaussianBumpDecomposition)
- [four scale Gaussian kernel]: [Todo] (Lean: fourScaleGaussianKernel)
- [mean four scale Gaussian kernel]: [Todo] (Lean: meanFourScaleGaussianKernel)

## The main argument

### The sandwich kernel

#### Definitions

- [geometric parameters]: [Completed] (Lean: GeometricParameters, sequencePairDistance, geometricDelta)
- [double sequence of 2D functions]: [Completed] (Lean: DoubleSequence, MemDoubleSequence)
- [kernel sequences]: [Completed] (Lean: KernelSequence, MemKernelSequence, kernelSequenceSeminorm)
- [2D Gaussians]: [Completed] (Lean: twoDimensionalGaussian, gammaGaussian)
- [sandwich kernel]: [Completed] (Lean: sandwichKernel)

#### Theorems

- [telescoping terms]: [Todo] (Lean: telescopingTerms)
- [positive terms]: [Todo] (Lean: positiveTerms)

### Multipliers $H$, $L$, $N$

#### Definitions

- [square root Gaussian difference]: [Completed] (Lean: squareRootGaussianDifference)
- [s multiplier]: [Completed] (Lean: sMultiplier)
- [H multiplier]: [Completed] (Lean: hMultiplier)
- [L multiplier]: [Completed] (Lean: multiplierIndexSet, lMultiplier)
- [summation-definition]: [Completed] (Lean: sumOverMultiplierIndex)
- [N multiplier]: [Completed] (Lean: sigmaMultiplier, nMultiplier)

#### Theorems

- [square root Gaussian difference W0]: [Todo] (Lean: squareRootGaussianDifference_memW0, sMultiplier_memW0)
- [H-in-X]: [Todo] (Lean: hMultiplier_memDoubleSequence)
- [H vanishing]: [Todo] (Lean: hMultiplier_vanishing)
- [H vanishing integral]: [Todo] (Lean: hMultiplier_vanishingIntegral)
- [L:F_t]: [Todo] (Lean: lMultiplierAtScale_memDoubleSequence, lMultiplierAtScale_tendsto_hMultiplier)
- [L:ft-infty]: [Todo] (Lean: lMultiplierAtScale_tendsto_zero)
- [sum L multiplier convergence-L1]: [Todo] (Lean: sumLMultiplierConvergenceL1)
- [sandwich sums L1]: [Todo] (Lean: sandwichSumsL1)
- [prism sum le sum prism-L1]: [Todo] (Lean: prismSumLeSumPrismL1)

### Gaussian domination

#### Definitions

#### Theorems

- [H kernel estimate Gaussian domination]: [Todo] (Lean: hKernelEstimateGaussianDomination)
- [H kernel derivative estimate Gaussian domination]: [Todo] (Lean: hKernelDerivativeEstimateGaussianDomination)
- [Gaussian domination combined]: [Todo] (Lean: gaussianDominationCombined)
- [Gauss domination case 1]: [Todo] (Lean: gaussDominationCase1)
- [Gauss domination case 2]: [Todo] (Lean: gaussDominationCase2)
- [Gauss domination case 3]: [Todo] (Lean: gaussDominationCase3)
- [Gauss domination constant]: [Todo] (Lean: gaussDominationConstant)

### Main induction

#### Definitions

- [induct positive terms]: [Completed] (Lean: InductPositiveTerms)
- [vanishing diagonal]: [Completed] (Lean: VanishingDiagonal)
- [diagonal band]: [Completed] (Lean: DiagonalBand)
- [increase data]: [Completed] (Lean: IncreaseData)

#### Theorems

- [vanishing diagonal implies induct positive terms]: [Todo] (Lean: vanishingDiagonal_implies_inductPositiveTerms)
- [diagonal band implies vanishing diagonal]: [Todo] (Lean: diagonalBand_implies_vanishingDiagonal)
- [vanishing kernel integral]: [Todo] (Lean: vanishingKernelIntegral)
- [increase data implies diagonal band]: [Todo] (Lean: increaseData_implies_diagonalBand)
- [induct positive terms imply increase data]: [Todo] (Lean: inductPositiveTerms_implies_increaseData)
- [P:C_k-induction]: [Todo] (Lean: inductPositiveTermsByInduction)
- [P:better-induction]: [Todo] (Lean: betterInduction)
- [induct positive terms theorem]: [Todo] (Lean: inductPositiveTermsTheorem)
