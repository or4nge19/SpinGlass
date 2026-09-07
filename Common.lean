import Common.Mathlib.Analysis.Calculus.BoundedFDerivGrowth
import Common.Mathlib.Analysis.Calculus.FDerivCLMComp
import Common.Mathlib.Analysis.Calculus.GradientAPI
import Common.Mathlib.Analysis.InnerProductSpace.PositiveInner
import Common.Mathlib.Analysis.MeanInequalities.WeightedAMGM
import Common.Mathlib.Analysis.Matrix.HadamardPow
import Common.Mathlib.Analysis.SpecialFunctions.Tanh
import Common.Mathlib.Analysis.Distribution.TemperateGrowthFDeriv
import Common.Mathlib.Analysis.SpecialFunctions.LogSumExp
import Common.Mathlib.MeasureTheory.ParametricDominatedConvergence
import Common.Mathlib.Probability.Distributions.Gaussian.CameronMartinAPI
import Common.Mathlib.Probability.Distributions.Gaussian.Real
import Common.Mathlib.Probability.Distributions.Gaussian.SubGaussian
import Common.Mathlib.Probability.Distributions.GaussianIntegrationByParts
import Common.Mathlib.Probability.Distributions.Gaussian_Divergence
import Common.Mathlib.Probability.Distributions.Gaussian_IBP2_Hilbert
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_Temperate
import Common.Mathlib.Probability.Distributions.Gaussian_ComparisonIndep
import Common.Mathlib.Probability.Distributions.Gaussian_Interpolation
import Common.Mathlib.Probability.Distributions.Gaussian_Rotation
import Common.Mathlib.Probability.Distributions.Gaussian_ProdCovariance
import Common.Mathlib.Probability.Distributions.Gaussian_SudakovFernique
import Common.Mathlib.Probability.Distributions.Gaussian_IBP_HilbertAPI

/-!
# Common

Parametric dominated convergence, Cameron–Martin / Fernique, sub-Gaussian bounds, and Gaussian
integration by parts: first order (`Gaussian_IBP_Hilbert`), second order / Price
(`Gaussian_IBP2_Hilbert`), the divergence–trace form (`Gaussian_Divergence`), and one-dimensional
(`GaussianIntegrationByParts`), and the `Function.HasTemperateGrowth` interface together with the
affine and linear-substitution trace identities (`Gaussian_IBP_Temperate`).
Import the `*API` modules downstream.
-/
