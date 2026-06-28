import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

structure MetaCICSubjectReductionObstructionWitnessUp : Type where
  beta : BHist
  appArg : BHist
  lamDomain : BHist
  piDomain : BHist
  matrix : BHist
  gap : BHist
  obstruction : BHist
  socket : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  namecert : BHist

end BEDC.Derived
