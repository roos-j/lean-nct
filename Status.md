# Formalization status

Definitions use `Todo` or `Completed`. Theorems use `Todo`, `Statement completed`, or `Proof completed`; the latter means that the proof is sorry-free and depends only on standard axioms.

## Introduction

Lean file: Introduction.lean

### Twisted averages

Lean file: Introduction.lean

#### Definitions

\label{A_def}: [Completed] (Lean: twistedAverage, twistedAverageAtScale) (2026-08-09 10:00:00 EDT)

#### Theorems

\label{thm:nct main real}: [Statement completed] (Lean: mainTwistedTheorem) (2026-08-09 10:00:00 EDT)

## Preliminaries

Lean file: Preliminaries

### Notation

Lean file: Preliminaries/Notation.lean

#### Definitions

\label{closed ball}: [Completed] (Lean: Metric.closedBall) (2026-08-09 10:00:00 EDT)
\label{gaussian}: [Completed] (Lean: Notation.gaussian) (2026-08-09 10:00:00 EDT)
\label{bracket bump}: [Completed] (Lean: Notation.bracketBump, Notation.scaledBracketBump, Notation.scaledBracketBumpReal) (2026-08-09 10:00:00 EDT)

### The Wiener space $W_0$

Lean file: WienerSpace.lean

#### Definitions

\label{auto:Wiener-space-definition}: [Completed] (Lean: wienerEnvelope, MemW0, wienerNorm, wienerNormOne) (2026-08-09 10:00:00 EDT)
\label{auto:convolution-along-vector-definition}: [Completed] (Lean: convolutionAlongVector) (2026-08-09 10:00:00 EDT)

#### Theorems

\label{auto:local-supremum-measurability}: [Proof completed] (Lean: localSupremumMeasurability) (2026-08-09 10:15:00 EDT)
\label{W_0 radius independence}: [Proof completed] (Lean: wienerNorm_le_max_one_three_mul_div_pow_mul, memW0_iff_integrable_wienerEnvelope) (2026-08-09 10:00:00 EDT)
\label{P:lp-embedding}: [Proof completed] (Lean: MemW0.memLp) (2026-08-09 10:00:00 EDT)
\label{W_0 fiber integrals}: [Proof completed] (Lean: exists_wienerEnvelope_fiber_and_integral_comp_injective_continuousLinearMap_bound) (2026-08-09 10:00:00 EDT)
\label{tensor Wiener}: [Proof completed] (Lean: MemW0.fintype_tensor, fintype_tensor_wienerNorm_le) (2026-08-09 10:00:00 EDT)
\label{W_0 Brascamp Lieb}: [Proof completed] (Lean: exists_brascamp_lieb_memW0) (2026-08-09 10:00:00 EDT)
\label{P:schwartz-into-wiener}: [Proof completed] (Lean: SchwartzMap.memW0) (2026-08-09 10:00:00 EDT)
\label{convolution vector}: [Proof completed] (Lean: memW0_convolutionAlongVector, fourier_convolutionAlongVector) (2026-08-09 10:00:00 EDT)

### K kernels

Lean file: Preliminaries/KKernels.lean

#### Definitions

\label{normalized function tuples}: [Completed] (Lean: normalizedFunctionTuples) (2026-08-09 10:00:00 EDT)
\label{cube Brascamp--Lieb}: [Completed] (Lean: cubeBrascampLiebForm) (2026-08-09 10:00:00 EDT)
\label{prism Brascamp--Lieb}: [Completed] (Lean: prismBrascampLiebForm) (2026-08-09 10:00:00 EDT)

#### Theorems

\label{cube BL inequality}: [Proof completed] (Lean: cubeBLInequality) (2026-08-09 10:00:00 EDT)
\label{prism BL inequality}: [Proof completed] (Lean: prismBLInequality) (2026-08-09 10:00:00 EDT)
\label{simplification 1 prism}: [Proof completed] (Lean: simplificationOnePrism) (2026-08-09 10:00:00 EDT)
\label{single cancellative Cauchy-Schwarz}: [Proof completed] (Lean: singlyCancellativeKernel_memW0, singlyCancellativeLift_memW0, singlyCancellativeCauchySchwarz_bound) (2026-08-09 10:00:00 EDT)
\label{doubly cancellative Cauchy-Schwarz}: [Proof completed] (Lean: doublyCancellativeKernel_memW0, doublyCancellativeLift_memW0, doublyCancellativeCauchySchwarz_bound) (2026-08-09 10:00:00 EDT)
\label{Positivity K}: [Proof completed] (Lean: positivityKernel_memW0, positivityKernel_nonnegative) (2026-08-09 10:00:00 EDT)
\label{Monotonicity K}: [Proof completed] (Lean: monotonicityK) (2026-08-09 10:00:00 EDT)

### M kernels

Lean file: Preliminaries/MKernels.lean

#### Definitions

\label{auto:prism-form-definition}: [Completed] (Lean: prismForm) (2026-08-09 10:00:00 EDT)

#### Theorems

\label{M to K}: [Proof completed] (Lean: mToK, mToK_integrand_memW0, mToK_memW0, mToK_eLpNorm_one_le) (2026-08-09 10:00:00 EDT)
\label{Positivity M}: [Proof completed] (Lean: positivityM_memW0, positivityM_nonnegative) (2026-08-09 10:00:00 EDT)
\label{Cauchy-Schwarz at k}: [Proof completed] (Lean: cauchySchwarzKernel_memW0, cauchySchwarzLift_memW0, cauchySchwarzAtK_bound) (2026-08-09 10:00:00 EDT)
\label{Cauchy-Schwarz at n-1}: [Proof completed] (Lean: doublyCauchySchwarzKernel_memW0, cauchySchwarzLift_memW0, cauchySchwarzAtNMinusOne_bound, cauchySchwarzAtNMinusOne) (2026-08-09 10:15:00 EDT)

### Multiplicatively spaced monotone sequences

Lean file: Preliminaries/MultiplicativelySpacedMonotoneSequences.lean

#### Definitions

\label{multiplicatively spaced monotone sequences}: [Completed] (Lean: SpacedSequence, A) (2026-08-09 10:00:00 EDT)
\label{Distance of spaced sequences}: [Completed] (Lean: WithinSequenceDistance, SequenceDistance) (2026-08-09 10:00:00 EDT)
\label{closed balls in A}: [Completed] (Lean: sequenceDistanceBall) (2026-08-09 10:00:00 EDT)

#### Theorems

\label{Extension of sequences}: [Proof completed] (Lean: extensionOfSequences) (2026-08-09 10:00:00 EDT)
\label{Operations on spaced sequences}: [Proof completed] (Lean: max_mem_A, smul_mem_A, shift_mem_A, sqrt_sq_add_sq_mem_A) (2026-08-09 10:00:00 EDT)
\label{Properties of distance of sequences}: [Proof completed] (Lean: sequenceDistance_zero_eq, sequenceDistance_comm, sequenceDistance_triangle, sequenceDistance_shift_le, sequenceDistance_smul, sequenceDistance_pow_two_smul_le) (2026-08-09 10:00:00 EDT)

### Gaussians

Lean file: Preliminaries/Gaussians.lean

#### Theorems

\label{square root one minus Gaussian}: [Proof completed] (Lean: sqrtOneMinusGaussian, sqrtOneMinusGaussian_wellDefined, continuous_sqrtOneMinusGaussian, sqrtOneMinusGaussian_lower, sqrtOneMinusGaussian_bounds) (2026-08-09 10:15:00 EDT)
\label{Gaussian bump decay}: [Proof completed] (Lean: gaussianBumpDecay) (2026-08-09 12:04:15 EDT)
\label{Elementary Gaussian properties}: [Proof completed] (Lean: gaussian_memSchwartz, gaussian_memW0, gaussian_fourier_fixed, gaussianRescale_convolution, gaussianRescale_fourier) (2026-08-09 10:45:23 EDT)
\label{poisson to abel}: [Proof completed] (Lean: poissonKernel, poissonKernel_fourier) (2026-08-09 10:00:00 EDT)
\label{auxiliary function B}: [Proof completed] (Lean: auxiliaryFunctionB_properties) (2026-08-10 16:29:54 EDT)
\label{square root of Gaussian decay}: [Proof completed] (Lean: sqrtGaussianDecay) (2026-08-10 16:29:54 EDT)

### Bumps and their estimates

Lean file: Preliminaries/BumpsAndEstimates.lean

#### Definitions

\label{standard bump}: [Completed] (Lean: standardBumpFinite, standardBump, standardBumpRescale) (2026-08-09 10:00:00 EDT)

#### Theorems

\label{lem:smoothdecay}: [Proof completed] (Lean: smoothDecay) (2026-08-09 21:56:52 EDT)
\label{lem: min and bracket}: [Proof completed] (Lean: min_and_bracket) (2026-08-09 22:50:13 EDT)
\label{lem:smoothdecay2}: [Proof completed] (Lean: smoothDecay2) (2026-08-09 22:08:34 EDT)
\label{mean value bump estimate 2}: [Proof completed] (Lean: meanValueBumpEstimate) (2026-08-10 16:46:10 EDT)
\label{standard bump properties}: [Proof completed] (Lean: standardBumpProperties, standardBumpProperties_l1Convergence, standardBumpProperties_linfConvergence, standardBumpProperties_schwartz, standardBumpProperties_fourierShape, standardBumpProperties_fourierDerivativeEstimate, standardBumpProperties_derivativeDecay) (2026-08-10 02:49:28 EDT)
\label{compare brackets}: [Proof completed] (Lean: compare_brackets) (2026-08-10 02:57:53 EDT)
\label{two bump estimate}: [Proof completed] (Lean: twoBumpEstimate) (2026-08-10 03:41:41 EDT)
\label{orthogonal domination}: [Proof completed] (Lean: orthogonalDomination) (2026-08-10 03:48:05 EDT)
\label{orthogonal decay}: [Proof completed] (Lean: orthogonalDecay) (2026-08-10 04:08:13 EDT)
\label{bump triangle}: [Proof completed] (Lean: bump_triangle) (2026-08-10 04:24:10 EDT)
\label{Gaussian domination}: [Proof completed] (Lean: gaussianDomination) (2026-08-10 04:51:38 EDT)
\label{diagonal square root}: [Proof completed] (Lean: diagonalSquareRoot, diagonalSquareRoot_bound, diagonalSquareRoot_memW0) (2026-08-10 06:51:06 EDT)
\label{constant diagonal square root}: [Proof completed] (Lean: constantDiagonalSquareRoot) (2026-08-10 16:53:44 EDT)
\label{derivative of diagonal square root}: [Proof completed] (Lean: derivativeDiagonalSquareRoot_differentiable, derivativeDiagonalSquareRoot_bound) (2026-08-10 07:23:38 EDT)
\label{constant derivative diagonal square root}: [Proof completed] (Lean: constantDerivativeDiagonalSquareRoot) (2026-08-10 16:53:44 EDT)
\label{L:gaussian-estimate}: [Proof completed] (Lean: gaussianEstimate) (2026-08-10 08:25:25 EDT)
\label{L:gaussian-bump-estimate}: [Proof completed] (Lean: gaussianBumpEstimate) (2026-08-10 08:33:21 EDT)
\label{constant gaussian bump estimate}: [Proof completed] (Lean: constantGaussianBumpEstimate) (2026-08-10 17:05:03 EDT)
\label{L:derivative-estimate-for-G}: [Proof completed] (Lean: derivativeEstimateForG) (2026-08-10 08:42:29 EDT)
\label{L:faa-di-bruno}: [Proof completed] (Lean: faaDiBruno) (2026-08-10 09:23:40 EDT)
\label{constant faa di bruno}: [Proof completed] (Lean: constantFaaDiBruno) (2026-08-10 18:40:53 EDT)
\label{L:second-gaussian-estimate}: [Proof completed] (Lean: secondGaussianEstimate) (2026-08-10 10:40:49 EDT)
\label{constant second gaussian estimate}: [Proof completed] (Lean: constantSecondGaussianEstimate) (2026-08-10 18:58:05 EDT)
\label{L:gaussian-bump-decomposition}: [Proof completed] (Lean: gaussianBumpDecomposition) (2026-08-10 10:56:01 EDT)
\label{four scale Gaussian kernel}: [Proof completed] (Lean: fourScaleGaussianKernel) (2026-08-10 11:09:38 EDT)
\label{constant four scale Gaussian kernel}: [Proof completed] (Lean: constantFourScaleGaussianKernel) (2026-08-10 19:05:22 EDT)
\label{mean four scale Gaussian kernel}: [Proof completed] (Lean: meanFourScaleGaussianKernel) (2026-08-10 11:45:23 EDT)
\label{constant mean four scale Gaussian kernel}: [Proof completed] (Lean: constantMeanFourScaleGaussianKernel) (2026-08-10 19:11:12 EDT)

## The main argument

Lean file: MainArgument

### The sandwich kernel

Lean file: MainArgument/SandwichKernel.lean

#### Definitions

\label{geometric parameters}: [Completed] (Lean: GeometricParameters, sequencePairDistance, geometricDelta) (2026-08-09 10:00:00 EDT)
\label{auto:unitary-matrices-definition}: [Completed] (Lean: W) (2026-08-09 10:00:00 EDT)
\label{double sequence of 2D functions}: [Completed] (Lean: DoubleSequence, MemDoubleSequence) (2026-08-09 10:00:00 EDT)
\label{kernel sequences}: [Completed] (Lean: KernelSequence, MemKernelSequence, kernelSequenceSeminorm) (2026-08-09 10:00:00 EDT)
\label{2D Gaussians}: [Completed] (Lean: twoDimensionalGaussian, gammaGaussian) (2026-08-09 10:00:00 EDT)
\label{sandwich kernel}: [Completed] (Lean: sandwichKernel) (2026-08-09 10:00:00 EDT)
\label{auto:Gaussian-difference-kernel-definition}: [Completed] (Lean: gaussianDifference) (2026-08-09 10:00:00 EDT)

#### Theorems

\label{telescoping terms}: [Proof completed] (Lean: telescopingTerms) (2026-08-10 23:06:21 EDT)
\label{positive terms}: [Proof completed] (Lean: positiveTerms) (2026-08-11 08:21:28 EDT)

### Multipliers $H$, $L$, $N$

Lean file: MainArgument/MultipliersHLN.lean

#### Definitions

\label{square root Gaussian difference}: [Completed] (Lean: squareRootGaussianDifference) (2026-08-09 10:00:00 EDT)
\label{s multiplier}: [Completed] (Lean: sMultiplier) (2026-08-09 10:00:00 EDT)
\label{H multiplier}: [Completed] (Lean: hMultiplier) (2026-08-09 10:00:00 EDT)
\label{auto:L-kernel-definition}: [Completed] (Lean: lMultiplierAtScale) (2026-08-09 10:00:00 EDT)
\label{L multiplier}: [Completed] (Lean: multiplierIndexSet, lMultiplier) (2026-08-09 10:00:00 EDT)
\label{summation-definition}: [Completed] (Lean: sumOverMultiplierIndex) (2026-08-09 10:00:00 EDT)
\label{N multiplier}: [Completed] (Lean: sigmaMultiplier, nMultiplier) (2026-08-09 10:00:00 EDT)

#### Theorems

\label{square root Gaussian difference W0}: [Proof completed] (Lean: squareRootGaussianDifference_memW0, sMultiplier_memW0) (2026-08-10 23:13:23 EDT)
\label{H-in-X}: [Proof completed] (Lean: hMultiplier_memDoubleSequence) (2026-08-10 23:18:44 EDT)
\label{H vanishing}: [Proof completed] (Lean: hMultiplier_fourier_diagonal_vanishing) (2026-08-10 23:51:09 EDT)
\label{H vanishing integral}: [Proof completed] (Lean: hMultiplier_vanishing_integral) (2026-08-11 00:08:24 EDT)
\label{L:F_t}: [Proof completed] (Lean: lMultiplierAtScale_memDoubleSequence, lMultiplierAtScale_tendsto_hMultiplier) (2026-08-11 01:08:56 EDT)
\label{L:ft-infty}: [Proof completed] (Lean: lMultiplierAtScale_tendsto_zero) (2026-08-11 01:51:17 EDT)
\label{sum L multiplier convergence-L1}: [Proof completed] (Lean: sumLMultiplierConvergenceL1) (2026-08-11 02:52:21 EDT)
\label{sandwich sums L1}: [Proof completed] (Lean: sandwichSumsL1) (2026-08-11 03:34:01 EDT)
\label{prism sum le sum prism-L1}: [Proof completed] (Lean: prismSumLeSumPrismL1) (2026-08-11 04:13:12 EDT)
\label{auto:N-kernel-well-definedness}: [Proof completed] (Lean: nKernelWellDefinedness) (2026-08-11 05:04:33 EDT)

### Gaussian domination

Lean file: MainArgument/GaussianDomination.lean

#### Theorems

\label{H kernel estimate Gaussian domination}: [Proof completed] (Lean: hKernelEstimateGaussianDomination) (2026-08-11 05:18:27 EDT)
\label{constant H kernel estimate Gaussian domination}: [Proof completed] (Lean: constantHKernelEstimateGaussianDomination) (2026-08-11 05:25:48 EDT)
\label{H kernel derivative estimate Gaussian domination}: [Proof completed] (Lean: hKernelDerivativeEstimateGaussianDomination) (2026-08-11 06:17:54 EDT)
\label{constant H kernel derivative estimate Gaussian domination}: [Proof completed] (Lean: constantHKernelDerivativeEstimateGaussianDomination) (2026-08-11 06:28:08 EDT)
\label{Gaussian domination combined}: [Proof completed] (Lean: gaussianDominationCombined) (2026-08-11 17:11:11 EDT)
\label{Gauss domination case 1}: [Proof completed] (Lean: gaussDominationCase1) (2026-08-11 11:16:34 EDT)
\label{Gauss domination case 2}: [Proof completed] (Lean: gaussDominationCase2) (2026-08-11 14:54:45 EDT)
\label{Gauss domination case 3}: [Proof completed] (Lean: gaussDominationCase3) (2026-08-11 16:46:00 EDT)
\label{Gauss domination constant}: [Proof completed] (Lean: gaussDominationConstant) (2026-08-11 17:02:34 EDT)

### Main induction

Lean file: MainArgument/MainInduction.lean

#### Definitions

\label{induct positive terms}: [Completed] (Lean: InductPositiveTerms) (2026-08-09 10:00:00 EDT)
\label{vanishing diagonal}: [Completed] (Lean: VanishingDiagonal) (2026-08-09 10:00:00 EDT)
\label{diagonal band}: [Completed] (Lean: DiagonalBand) (2026-08-09 10:00:00 EDT)
\label{increase data}: [Completed] (Lean: IncreaseData) (2026-08-09 10:00:00 EDT)

#### Theorems

\label{vanishing diagonal implies induct positive terms}: [Proof completed] (Lean: vanishingDiagonal_implies_inductPositiveTerms) (2026-08-11 18:34:43 EDT)
\label{diagonal band implies vanishing diagonal}: [Proof completed] (Lean: diagonalBand_implies_vanishingDiagonal) (2026-08-11 18:56:18 EDT)
\label{vanishing kernel integral}: [Proof completed] (Lean: vanishingKernelIntegral) (2026-08-11 18:34:43 EDT)
\label{increase data implies diagonal band}: [Proof completed] (Lean: increaseData_implies_diagonalBand) (2026-08-12 01:11:23 EDT)
\label{induct positive terms imply increase data}: [Proof completed] (Lean: inductPositiveTerms_implies_increaseData) (2026-08-12 00:22:35 EDT)
\label{constant induct positive terms imply increase data}: [Proof completed] (Lean: constantInductPositiveTermsImplyIncreaseData) (2026-08-11 17:19:57 EDT)
\label{P:C_k-induction}: [Proof completed] (Lean: inductPositiveTermsByInduction) (2026-08-12 01:11:23 EDT)
\label{P:better-induction}: [Proof completed] (Lean: betterInduction) (2026-08-12 07:12:24 EDT)
\label{induct positive terms theorem}: [Proof completed] (Lean: inductPositiveTermsTheorem) (2026-08-12 07:12:24 EDT)
\label{constant induct positive terms theorem}: [Proof completed] (Lean: constantInductPositiveTermsTheorem) (2026-08-11 17:37:33 EDT)

## Reduction to the main argument

Lean file: Reduction

### Further preliminaries for the reduction / Average to prism form

Lean file: Reduction/AToLambda.lean

#### Theorems

\label{A to Lambda}: [Proof completed] (Lean: aToLambda) (2026-08-12 09:41:23 EDT)

### Further preliminaries for the reduction / Variation seminorms

Lean file: Reduction/VariationSeminorms.lean

#### Theorems

\label{lem:shortlongjumps}: [Proof completed] (Lean: shortlongJumps) (2026-08-12 10:35:57 EDT)
\label{lem:ftccs-R}: [Proof completed] (Lean: ftcCsR) (2026-08-12 11:32:21 EDT)

### Further preliminaries for the reduction / Bump functions

Lean file: Reduction/BumpFunctions.lean

#### Theorems

\label{lem:ft_deriv_mul}: [Proof completed] (Lean: fourierDerivativeMul) (2026-08-12 11:35:51 EDT)
\label{lem:widebump}: [Proof completed] (Lean: wideBump) (2026-08-12 11:40:49 EDT)
\label{lem:thetat_offcenter}: [Proof completed] (Lean: thetaTOffcenter) (2026-08-12 17:29:38 PDT)
\label{constant off center bump}: [Proof completed] (Lean: constantOffCenterBump) (2026-08-12 17:45:41 PDT)
\label{lem:int_fct}: [Proof completed] (Lean: integralFct) (2026-08-12 22:22:46 PDT)
\label{lem:Phipos_v2}: [Proof completed] (Lean: phiPosV2) (2026-08-12 22:22:46 PDT)

### Further preliminaries for the reduction / Windows and pairs

Lean file: Reduction/WindowsAndPairs.lean

#### Definitions

\label{def:cn-window}: [Completed] (Lean: cnWindow) (2026-08-12 08:32:42 EDT)
\label{def:cpair}: [Completed] (Lean: cPair) (2026-08-12 08:32:42 EDT)
\label{def:unipair}: [Completed] (Lean: uniPair) (2026-08-12 08:32:42 EDT)
\label{def:window}: [Completed] (Lean: window) (2026-08-12 08:32:42 EDT)

#### Theorems

\label{lem:cpair}: [Proof completed] (Lean: existsUniversalPair) (2026-08-13 07:20:57 PDT)

### Further preliminaries for the reduction / A smoothing decomposition

Lean file: Reduction/SmoothingDecomposition.lean

#### Definitions

\label{defn:window based bump functions}: [Completed] (Lean: windowBasedBumpFunctions) (2026-08-12 08:32:42 EDT)

#### Theorems

\label{lem:bumpbasic}: [Proof completed] (Lean: bumpBasic) (2026-08-13 07:25:45 PDT)
\label{lem:chardecomp}: [Proof completed] (Lean: charDecomp) (2026-08-13 08:02:56 PDT)
\label{lem:smoothingdecomp}: [Proof completed] (Lean: smoothingDecomp) (2026-08-13 08:44:24 PDT)
\label{lem:theta_decay}: [Proof completed] (Lean: thetaDecay) (2026-08-13 09:02:35 PDT)
\label{constant theta decay}: [Proof completed] (Lean: constantThetaDecay) (2026-08-13 09:06:04 PDT)
\label{lem:ft_phi3_eq}: [Proof completed] (Lean: fourierPhiThreeEq) (2026-08-13 09:14:16 PDT)
\label{lem:abs_deriv_ft_phi3_le}: [Proof completed] (Lean: absDerivFourierPhiThreeLe) (2026-08-13 10:02:27 PDT)
\label{constant phi three derivative}: [Proof completed] (Lean: constantPhiThreeDerivative) (2026-08-13 09:15:16 PDT)
\label{lem:abs_deriv_ft_Tphi3_le}: [Proof completed] (Lean: absDerivFourierTPhiThreeLe) (2026-08-13 10:40:13 PDT)
\label{constant T phi three derivative}: [Proof completed] (Lean: constantTPhiThreeDerivative) (2026-08-13 09:18:37 PDT)
\label{lem:theta_prim}: [Proof completed] (Lean: thetaPrimitive) (2026-08-13 10:00:00 PDT)
\label{constant theta primitive}: [Proof completed] (Lean: constantThetaPrimitive) (2026-08-13 10:00:00 PDT)
\label{lem:phi4_supp}: [Proof completed] (Lean: phiFourSupport) (2026-08-13 10:42:02 PDT)

### Further preliminaries for the reduction / Miscellany

Lean file: Reduction/Miscellany.lean

#### Theorems

\label{lem:rescaling}: [Proof completed] (Lean: rescaling) (2026-08-13 10:49:06 PDT)
\label{lem:norm_A_sum_le_sum}: [Proof completed] (Lean: normASumLeSum) (2026-08-13 12:12:09 PDT)
\label{lem:form_pos}: [Proof completed] (Lean: formPos) (2026-08-13 11:44:15 PDT)
\label{lem:ftc_ATphi}: [Proof completed] (Lean: ftcATphi) (2026-08-13 12:40:41 PDT)
\label{lem:Phij_prop}: [Proof completed] (Lean: phiJProperties) (2026-08-13 15:17:44 PDT)
\label{constant Phij proposition}: [Proof completed] (Lean: constantPhiJProposition) (2026-08-13 15:17:44 PDT)
\label{lem:bootstrap}: [Proof completed] (Lean: bootstrap) (2026-08-13 15:17:44 PDT)

### On-diagonal from main argument

Lean file: Reduction/OnDiagonalMainArgument.lean

#### Theorems

\label{lem:rho-kernels-reduction}: [Proof completed] (Lean: rhoKernelsReduction) (2026-08-13 21:30:00 PDT)
\label{constant rho kernels reduction}: [Proof completed] (Lean: constantRhoKernelsReduction) (2026-08-13 21:30:00 PDT)
\label{lem:affine-diagonal-cancellation-reduction}: [Proof completed] (Lean: affineDiagonalCancellationReduction) (2026-08-13 21:36:55 PDT)
\label{lem:increase-data-bracket-domination}: [Proof completed] (Lean: increaseDataBracketDomination) (2026-08-13 23:25:27 PDT)
\label{constant increase data bracket domination}: [Proof completed] (Lean: constantIncreaseDataBracketDomination) (2026-08-13 23:27:33 PDT)
\label{lem:increase-data-Gaussian-expansion}: [Proof completed] (Lean: increaseDataGaussianExpansion) (2026-08-13 23:47:19 PDT)
\label{constant increase data Gaussian expansion}: [Proof completed] (Lean: constantIncreaseDataGaussianExpansion) (2026-08-13 23:55:18 PDT)
\label{lem:N-reduction}: [Proof completed] (Lean: nReduction) (2026-08-14 00:17:39 PDT)
\label{constant N reduction}: [Proof completed] (Lean: constantNReduction) (2026-08-14 00:20:31 PDT)
\label{P:increase-data-reduction}: [Proof completed] (Lean: increaseDataReduction) (2026-08-14 01:57:53 PDT)
\label{constant increase data reduction}: [Proof completed] (Lean: constantIncreaseDataReduction) (2026-08-14 02:02:50 PDT)

### On-diagonal from off-diagonal estimates

Lean file: Reduction/OnDiagonalOffDiagonal.lean

#### Theorems

\label{P:diagonal-band-reduction}: [Proof completed] (Lean: diagonalBandReduction) (2026-08-14 02:57:01 PDT)
\label{constant diagonal band reduction}: [Proof completed] (Lean: constantDiagonalBandReduction) (2026-08-14 03:05:39 PDT)
\label{lem:L1-reduction}: [Proof completed] (Lean: lOneReduction) (2026-08-14 03:09:06 PDT)
\label{P:vanishing-diagonal-reduction}: [Proof completed] (Lean: vanishingDiagonalReduction) (2026-08-14 03:27:33 PDT)
\label{P:one-scale-estimate-window}: [Proof completed] (Lean: oneScaleEstimateWindow) (2026-08-14 03:38:44 PDT)
\label{auto:constant-one-scale-window}: [Proof completed] (Lean: constantOneScaleWindow) (2026-08-14 03:41:09 PDT)
\label{L:fourier-transform-window}: [Proof completed] (Lean: fourierTransformWindow) (2026-08-14 03:44:52 PDT)
\label{lem:scaleest}: [Proof completed] (Lean: scaleEstimate) (2026-08-14 03:46:49 PDT)
\label{P:induct-positive-terms-reduction-non-whitney}: [Proof completed] (Lean: inductPositiveTermsReductionNonWhitney) (2026-08-14 04:35:44 PDT)
\label{constant non Whitney reduction}: [Proof completed] (Lean: constantNonWhitneyReduction) (2026-08-14 04:37:42 PDT)
\label{P:induct-positive-terms-reduction-non-whitney-skip}: [Proof completed] (Lean: inductPositiveTermsReductionNonWhitneySkip) (2026-08-14 04:43:42 PDT)
\label{constant non Whitney skip reduction}: [Proof completed] (Lean: constantNonWhitneySkipReduction) (2026-08-14 04:46:33 PDT)
\label{P:induct-positive-terms-reduction-whitney-gap}: [Proof completed] (Lean: inductPositiveTermsReductionWhitneyGap) (2026-08-14 05:46:48 PDT)
\label{constant Whitney gap reduction}: [Proof completed] (Lean: constantWhitneyGapReduction) (2026-08-14 05:49:39 PDT)
\label{P:induct-positive-terms-reduction-whitney}: [Proof completed] (Lean: inductPositiveTermsReductionWhitney) (2026-08-14 05:53:18 PDT)
\label{constant Whitney reduction}: [Proof completed] (Lean: constantWhitneyReduction) (2026-08-14 05:55:51 PDT)
\label{P:induct-positive-terms-reduction-whitney-product}: [Proof completed] (Lean: inductPositiveTermsReductionWhitneyProduct) (2026-08-14 06:03:24 PDT)
\label{constant Whitney product reduction}: [Proof completed] (Lean: constantWhitneyProductReduction) (2026-08-14 06:03:24 PDT)

### Final reduction: proof of main theorem

Lean file: Reduction/FinalReduction.lean

#### Theorems

\label{lem:main_aux1}: [Statement completed] (Lean: mainAuxOne) (2026-08-12 08:32:42 EDT)
\label{constant main auxiliary one}: [Statement completed] (Lean: constantMainAuxiliaryOne) (2026-08-12 08:32:42 EDT)
\label{lem:shortlongftc_reduction}: [Statement completed] (Lean: shortLongFtcReduction) (2026-08-12 08:32:42 EDT)
\label{lem:mainbump1_long1}: [Statement completed] (Lean: mainBumpOneLongOne) (2026-08-12 08:32:42 EDT)
\label{constant main bump one long one}: [Statement completed] (Lean: constantMainBumpOneLongOne) (2026-08-12 08:32:42 EDT)
\label{lem:mainbump1_long2}: [Statement completed] (Lean: mainBumpOneLongTwo) (2026-08-12 08:32:42 EDT)
\label{constant main bump one long two}: [Statement completed] (Lean: constantMainBumpOneLongTwo) (2026-08-12 08:32:42 EDT)
\label{lem:mainbump1_long}: [Statement completed] (Lean: mainBumpOneLong) (2026-08-12 08:32:42 EDT)
\label{constant main bump one long}: [Statement completed] (Lean: constantMainBumpOneLong) (2026-08-12 08:32:42 EDT)
\label{lem:mainbump1}: [Statement completed] (Lean: mainBumpOne) (2026-08-12 08:32:42 EDT)
\label{constant main bump one}: [Statement completed] (Lean: constantMainBumpOne) (2026-08-12 08:32:42 EDT)
\label{lem:main_aux2}: [Statement completed] (Lean: mainAuxTwo) (2026-08-12 08:32:42 EDT)
\label{constant main auxiliary two}: [Statement completed] (Lean: constantMainAuxiliaryTwo) (2026-08-12 08:32:42 EDT)
\label{lem:mainbump2}: [Statement completed] (Lean: mainBumpTwo) (2026-08-12 08:32:42 EDT)
\label{constant main bump two}: [Statement completed] (Lean: constantMainBumpTwo) (2026-08-12 08:32:42 EDT)
\label{lem:leftbump}: [Statement completed] (Lean: leftBump) (2026-08-12 08:32:42 EDT)
\label{constant left bump}: [Statement completed] (Lean: constantLeftBump) (2026-08-12 08:32:42 EDT)
\label{lem:leftbump1_short1}: [Statement completed] (Lean: leftBumpOneShortOne) (2026-08-12 08:32:42 EDT)
\label{constant left bump one short one}: [Statement completed] (Lean: constantLeftBumpOneShortOne) (2026-08-12 08:32:42 EDT)
\label{lem:leftbump1_short2}: [Statement completed] (Lean: leftBumpOneShortTwo) (2026-08-12 08:32:42 EDT)
\label{constant left bump one short two}: [Statement completed] (Lean: constantLeftBumpOneShortTwo) (2026-08-12 08:32:42 EDT)
\label{lem:leftbump1_long}: [Statement completed] (Lean: leftBumpOneLong) (2026-08-12 08:32:42 EDT)
\label{constant left bump one long}: [Statement completed] (Lean: constantLeftBumpOneLong) (2026-08-12 08:32:42 EDT)
\label{lem:leftbump1}: [Statement completed] (Lean: leftBumpOne) (2026-08-12 08:32:42 EDT)
\label{constant left bump one}: [Statement completed] (Lean: constantLeftBumpOne) (2026-08-12 08:32:42 EDT)
