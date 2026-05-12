import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FibonacciCubeUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FibonacciCubePacket [AskSetup] [PackageSetup]
    (length path word support provenance deps nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory length ∧ UnaryHistory path ∧ UnaryHistory word ∧ UnaryHistory support ∧
    UnaryHistory provenance ∧ UnaryHistory deps ∧ UnaryHistory nameRow ∧
      Cont length path word ∧ Cont support provenance deps ∧ Cont deps nameRow nameRow ∧
        PkgSig bundle nameRow pkg

theorem FibonacciCubePacket_carrier_habitation [AskSetup] [PackageSetup]
    {length path word support provenance deps nameRow emptySupport zeroWord : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FibonacciCubePacket length path word support provenance deps nameRow bundle pkg ->
      hsame support emptySupport ->
        hsame word zeroWord ->
          UnaryHistory length ∧ UnaryHistory path ∧ UnaryHistory emptySupport ∧
            UnaryHistory zeroWord ∧ hsame support emptySupport ∧ hsame word zeroWord ∧
              Cont length path word ∧ PkgSig bundle nameRow pkg := by
  intro packet sameSupport sameWord
  obtain ⟨lengthUnary, pathUnary, wordUnary, supportUnary, _provenanceUnary, _depsUnary,
    _nameUnary, pathWordRow, _depsRow, _nameRow, namePkg⟩ := packet
  have emptySupportUnary : UnaryHistory emptySupport :=
    unary_transport supportUnary sameSupport
  have zeroWordUnary : UnaryHistory zeroWord :=
    unary_transport wordUnary sameWord
  exact
    ⟨lengthUnary, pathUnary, emptySupportUnary, zeroWordUnary, sameSupport, sameWord,
      pathWordRow, namePkg⟩

end BEDC.Derived.FibonacciCubeUp
