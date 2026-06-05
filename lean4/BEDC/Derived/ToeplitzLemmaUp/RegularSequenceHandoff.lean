import BEDC.Derived.ToeplitzLemmaUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ToeplitzLemmaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ToeplitzLemmaCarrier [AskSetup] [PackageSetup]
    (A W R D T E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory A ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory T ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem ToeplitzLemmaRegularSequenceHandoff [AskSetup] [PackageSetup]
    {A W R D T E H C P N sourceRead regularRead transformedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToeplitzLemmaCarrier A W R D T E H C P N bundle pkg →
      Cont A W sourceRead →
        Cont sourceRead R regularRead →
          Cont regularRead T transformedRead →
            Cont transformedRead E sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                        hsame row T ∨ hsame row E ∨ hsame row sourceRead ∨
                          hsame row regularRead ∨ hsame row transformedRead ∨
                            hsame row sealRead)
                    (fun row : BHist =>
                      hsame row sealRead ∧ Cont A W sourceRead ∧
                        Cont sourceRead R regularRead ∧
                          Cont regularRead T transformedRead ∧
                            Cont transformedRead E sealRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle sealRead pkg)
                    hsame ∧ UnaryHistory sourceRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory transformedRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute regularRoute transformedRoute sealRoute sealPkg
  obtain ⟨aUnary, wUnary, rUnary, _dUnary, tUnary, eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, provenancePkg, _namePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed aUnary wUnary sourceRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed sourceUnary rUnary regularRoute
  have transformedUnary : UnaryHistory transformedRead :=
    unary_cont_closed regularUnary tUnary transformedRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed transformedUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row T ∨
              hsame row E ∨ hsame row sourceRead ∨ hsame row regularRead ∨
                hsame row transformedRead ∨ hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont A W sourceRead ∧ Cont sourceRead R regularRead ∧
              Cont regularRead T transformedRead ∧ Cont transformedRead E sealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg)
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, sourceRoute, regularRoute, transformedRoute, sealRoute,
          provenancePkg, sealPkg⟩
  }
  exact ⟨cert, sourceUnary, regularUnary, transformedUnary, sealUnary⟩

end BEDC.Derived.ToeplitzLemmaUp
