import BEDC.Derived.SubnetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubnetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SubnetCarrier [AskSetup] [PackageSetup]
    (I X J phi T V L H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory I ∧ UnaryHistory X ∧ UnaryHistory J ∧ UnaryHistory phi ∧ UnaryHistory T ∧
    UnaryHistory V ∧ UnaryHistory L ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont J phi T ∧ Cont T X V ∧ Cont V L C ∧ PkgSig bundle P pkg ∧
        PkgSig bundle N pkg

theorem SubnetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {I X J phi T V L H C P N tailRead valueRead convergenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubnetCarrier I X J phi T V L H C P N bundle pkg ->
      Cont J phi tailRead ->
        Cont tailRead X valueRead ->
          Cont valueRead L convergenceRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row convergenceRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row I ∨ hsame row X ∨ hsame row J ∨ hsame row phi ∨
                        hsame row T ∨ hsame row V ∨ hsame row L ∨
                          hsame row convergenceRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont J phi tailRead ∧ Cont tailRead X valueRead ∧
                        Cont valueRead L convergenceRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle N pkg)
                    hsame ∧ UnaryHistory tailRead ∧ UnaryHistory valueRead ∧
                  UnaryHistory convergenceRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier tailRoute valueRoute convergenceRoute pkgP pkgN
  obtain ⟨_iUnary, xUnary, jUnary, phiUnary, _tUnary, _vUnary, lUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _carrierTail, _carrierValue, _carrierConvergence, _carrierPkgP,
    _carrierPkgN⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed jUnary phiUnary tailRoute
  have valueUnary : UnaryHistory valueRead :=
    unary_cont_closed tailUnary xUnary valueRoute
  have convergenceUnary : UnaryHistory convergenceRead :=
    unary_cont_closed valueUnary lUnary convergenceRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row convergenceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row X ∨ hsame row J ∨ hsame row phi ∨
              hsame row T ∨ hsame row V ∨ hsame row L ∨ hsame row convergenceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont J phi tailRead ∧ Cont tailRead X valueRead ∧
              Cont valueRead L convergenceRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro convergenceRead ⟨hsame_refl convergenceRead, convergenceUnary⟩
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
      exact ⟨source.right, tailRoute, valueRoute, convergenceRoute, pkgP, pkgN⟩
  }
  exact ⟨cert, tailUnary, valueUnary, convergenceUnary, pkgP, pkgN⟩

end BEDC.Derived.SubnetUp
