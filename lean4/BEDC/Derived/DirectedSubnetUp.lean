import BEDC.Derived.DirectedSubnetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DirectedSubnetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DirectedSubnetCarrier [AskSetup] [PackageSetup]
    (I J phi K L S R D A H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory I ∧ UnaryHistory J ∧ UnaryHistory phi ∧ UnaryHistory K ∧
    UnaryHistory L ∧ UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧
      UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
        UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem DirectedSubnetNameCertObligations [AskSetup] [PackageSetup]
    {I J phi K L S R D A H C P N targetRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSubnetCarrier I J phi K L S R D A H C P N bundle pkg →
      Cont K phi targetRead →
        Cont targetRead A sealRead →
          PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row I ∨ hsame row J ∨ hsame row phi ∨ hsame row K ∨
                    hsame row L ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                      hsame row A ∨ hsame row N)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory targetRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier routeTarget routeSeal namePkg
  obtain ⟨_unaryI, _unaryJ, unaryPhi, unaryK, _unaryL, _unaryS, _unaryR,
    _unaryD, unaryA, _unaryH, _unaryC, _unaryP, unaryN, provenancePkg,
    _carrierNamePkg⟩ := carrier
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed unaryK unaryPhi routeTarget
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed targetUnary unaryA routeSeal
  have sourceN :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row J ∨ hsame row phi ∨ hsame row K ∨
              hsame row L ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                hsame row A ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceN
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, targetUnary, sealUnary⟩

theorem DirectedSubnetCarrier_cauchynet_handoff [AskSetup] [PackageSetup]
    {I J phi K L S R D A H C P N targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DirectedSubnetCarrier I J phi K L S R D A H C P N bundle pkg →
      Cont K phi targetRead →
        UnaryHistory targetRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig
  intro carrier route
  obtain ⟨_unaryI, _unaryJ, unaryPhi, unaryK, _unaryL, _unaryS, _unaryR,
    _unaryD, _unaryA, _unaryH, _unaryC, _unaryP, _unaryN, provenancePkg,
    namePkg⟩ := carrier
  exact ⟨unary_cont_closed unaryK unaryPhi route, provenancePkg, namePkg⟩

end BEDC.Derived.DirectedSubnetUp
