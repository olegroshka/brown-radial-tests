import Radial
import Gaussian
import Rays
import Capacity
import Comparability
import Variance
import Polar
import Resistance
import Remainder
import LatticeRegularity
import SphericalA2
import WeightedBalls
import GaussianMarginal
import MultivariateGaussian
import GaussianSmooth
import LatticeGeometry
import SphereTest
import RayTest
import RayToll
import OneDim
import LatticeSeparation
import LatticeVolume
import PaperTheorems
import DoublingPoincare
import LatticeLocal
import CubePartition
import Gluing
import LatticeSmallBalls
import LatticeCovering
import LatticeDP
import LebesguePoincare
import CircleLocal
import CubeGrid
import CircleLemma
import ThmBFinal
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    if Name.isPrefixOf `BrownRadial name && getOriginalConstKind? env name == some .thm then
      let deps ← collectAxioms name
      for dep in deps do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dep do
          throwError "Unapproved dependency in {name}: {dep}"
      logInfo m!"CHECKED {name}: {deps}"
      count := count + 1
  if count == 0 then throwError "No project theorems were audited"
  logInfo m!"PASS: {count} theorem declarations; only approved foundations"
