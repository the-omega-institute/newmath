import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EffectiveModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EffectiveModulusCarrier [AskSetup] [PackageSetup]
    (source schedule modulus regularRow sealRow transport route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory schedule ∧ UnaryHistory modulus ∧
    UnaryHistory regularRow ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        Cont transport route provenance ∧ PkgSig bundle nameRow pkg

theorem EffectiveModulusCarrier_regular_cauchy_handoff [AskSetup] [PackageSetup]
    {source schedule modulus regularRow sealRow transport route provenance nameRow regularRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EffectiveModulusCarrier source schedule modulus regularRow sealRow transport route provenance
        nameRow bundle pkg ->
      Cont source schedule regularRead ->
        Cont regularRead modulus sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row schedule ∨ hsame row modulus ∨
                    hsame row regularRow ∨ hsame row sealRow ∨ hsame row regularRead ∨
                      hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont source schedule regularRead ∧
                    Cont regularRead modulus sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory regularRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont Pkg NameCert SemanticNameCert
  intro carrier regularRoute sealRoute sealPkg
  obtain ⟨sourceUnary, scheduleUnary, modulusUnary, _regularRowUnary, _sealRowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameUnary, _provenanceRoute,
    _namePkg⟩ := carrier
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed sourceUnary scheduleUnary regularRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary modulusUnary sealRoute
  have sourceSealRead :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  have core :
      NameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro sealRead sourceSealRead
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _other _third sameRO sameOT
        exact hsame_trans sameRO sameOT
      carrier_respects_equiv := by
        intro _row _other same source
        have sameOtherSeal : hsame _other sealRead :=
          hsame_trans (hsame_symm same) source.left
        have otherUnary : UnaryHistory _other :=
          unary_transport source.right same
        exact ⟨sameOtherSeal, otherUnary⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row schedule ∨ hsame row modulus ∨
              hsame row regularRow ∨ hsame row sealRow ∨ hsame row regularRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source schedule regularRead ∧
              Cont regularRead modulus sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro row source
        exact ⟨source.right, regularRoute, sealRoute, sealPkg⟩
    }
  exact ⟨cert, regularReadUnary, sealReadUnary⟩

end BEDC.Derived.EffectiveModulusUp
