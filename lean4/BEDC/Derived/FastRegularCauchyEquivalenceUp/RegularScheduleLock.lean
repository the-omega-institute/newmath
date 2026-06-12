import BEDC.Derived.FastRegularCauchyEquivalenceUp.NameCertObligations
import BEDC.FKernel.NameCert

namespace BEDC.Derived.FastRegularCauchyEquivalenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastRegularCauchyEquivalenceRegularScheduleLock [AskSetup] [PackageSetup]
    {fast stream dyadic regularRow realSeal transportRow replay provenance localName
      scheduleRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastRegularCauchyEquivalenceCarrier fast stream dyadic regularRow realSeal transportRow
        replay provenance localName bundle pkg ->
      Cont stream dyadic scheduleRead ->
        Cont scheduleRead regularRow regularRead ->
          Cont regularRead realSeal sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row fast ∨ hsame row stream ∨ hsame row dyadic ∨
                        hsame row regularRow ∨ hsame row realSeal ∨ hsame row scheduleRead ∨
                          hsame row regularRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont stream dyadic scheduleRead ∧
                        Cont scheduleRead regularRow regularRead ∧
                          Cont regularRead realSeal sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                UnaryHistory scheduleRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier scheduleRoute regularRoute sealRoute sealPkg
  obtain ⟨_fastUnary, streamUnary, dyadicUnary, regularUnary, realSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _provenancePkg,
    _localNamePkg⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed streamUnary dyadicUnary scheduleRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed scheduleUnary regularUnary regularRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary realSealUnary sealRoute
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row fast ∨ hsame row stream ∨ hsame row dyadic ∨ hsame row regularRow ∨
              hsame row realSeal ∨ hsame row scheduleRead ∨ hsame row regularRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont stream dyadic scheduleRead ∧
              Cont scheduleRead regularRow regularRead ∧ Cont regularRead realSeal sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, scheduleRoute, regularRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, scheduleUnary, regularReadUnary, sealReadUnary⟩

end BEDC.Derived.FastRegularCauchyEquivalenceUp
