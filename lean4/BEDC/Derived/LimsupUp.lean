import BEDC.Derived.LimsupUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LimsupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LimsupCarrier [AskSetup] [PackageSetup]
    (S U D T H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory S ∧ UnaryHistory U ∧ UnaryHistory D ∧ UnaryHistory T ∧
    UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
      Cont S U H ∧ Cont H D C ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

def LimsupClassifier
    (S U D T H C P N S' U' D' T' H' C' P' N' : BHist) : Prop :=
  hsame S S' ∧ hsame U U' ∧ hsame D D' ∧ hsame T T' ∧
    hsame H H' ∧ hsame C C' ∧ hsame P P' ∧ hsame N N'

theorem LimsupNameCertObligations [AskSetup] [PackageSetup]
    {S U D T H C P N upperRead lowerRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LimsupCarrier S U D T H C P N bundle pkg →
      LimsupClassifier S U D T H C P N S U D T H C P N →
        Cont S U upperRead →
          Cont upperRead D lowerRead →
            Cont lowerRead T sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row T ∨
                        hsame row upperRead ∨ hsame row lowerRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S U upperRead ∧
                        Cont upperRead D lowerRead ∧ Cont lowerRead T sealRead ∧
                          PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory upperRead ∧ UnaryHistory lowerRead ∧
                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier _classifier upperRoute lowerRoute sealRoute sealPkg
  obtain ⟨sUnary, uUnary, dUnary, tUnary, _hUnary, _cUnary, _nUnary,
    _sourceUpperTransport, _transportLedgerReplay, provenancePkg, _namePkg⟩ := carrier
  have upperUnary : UnaryHistory upperRead :=
    unary_cont_closed sUnary uUnary upperRoute
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed upperUnary dUnary lowerRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed lowerUnary tUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row U ∨ hsame row D ∨ hsame row T ∨
              hsame row upperRead ∨ hsame row lowerRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S U upperRead ∧ Cont upperRead D lowerRead ∧
              Cont lowerRead T sealRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, upperRoute, lowerRoute, sealRoute, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, upperUnary, lowerUnary, sealUnary⟩

end BEDC.Derived.LimsupUp
