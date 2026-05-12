import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyInterleaveUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyInterleavePacket [AskSetup] [PackageSetup]
    (left right merge windows modulus observations handoff transports routes provenance
      nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory merge ∧ UnaryHistory windows ∧
    UnaryHistory modulus ∧ UnaryHistory observations ∧ UnaryHistory handoff ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont merge windows observations ∧
          Cont modulus observations handoff ∧ Cont routes provenance nameCert ∧
            PkgSig bundle handoff pkg

theorem RegularCauchyInterleavePacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {left right merge windows modulus observations handoff transports routes provenance
      nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleavePacket left right merge windows modulus observations handoff
        transports routes provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyInterleavePacket left right merge windows modulus observations handoff
              transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          RegularCauchyInterleavePacket left right merge windows modulus observations handoff
              transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          RegularCauchyInterleavePacket left right merge windows modulus observations handoff
              transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro packet (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

def RegularCauchyInterleaveCarrier [AskSetup] [PackageSetup]
    (I J S T W D M H C P N endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory S ∧ UnaryHistory T ∧
    UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory endpoint ∧
        Cont I S T ∧ Cont T W D ∧ Cont D M endpoint ∧ PkgSig bundle endpoint pkg

theorem RegularCauchyInterleaveWindowMergeExactness [AskSetup] [PackageSetup]
    {I J S T W D M H C P N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyInterleaveCarrier I J S T W D M H C P N endpoint bundle pkg ->
      UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory S ∧ UnaryHistory T ∧
        UnaryHistory W ∧ UnaryHistory D ∧ Cont I S T ∧ Cont T W D ∧
          Cont D M endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier
  obtain ⟨iUnary, jUnary, sUnary, tUnary, wUnary, dUnary, _mUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _endpointUnary, sourceWindow, windowDyadic,
    dyadicHandoff, pkgSig⟩ := carrier
  exact
    ⟨iUnary, jUnary, sUnary, tUnary, wUnary, dUnary, sourceWindow, windowDyadic,
      dyadicHandoff, pkgSig⟩

end BEDC.Derived.RegularCauchyInterleaveUp
