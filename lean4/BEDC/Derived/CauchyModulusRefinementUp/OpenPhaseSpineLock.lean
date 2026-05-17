import BEDC.Derived.CauchyModulusRefinementUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_open_phase_spine_lock [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n dyadic stream regseq real endpoint hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      UnaryHistory regseq →
        Cont w regseq stream →
          Cont q stream dyadic →
            Cont q e real →
              Cont real p endpoint →
                PkgSig bundle endpoint pkg →
                  SemanticNameCert
                    (fun row : BHist =>
                      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n
                          bundle pkg ∧
                        hsame row endpoint)
                    (fun row : BHist =>
                      Cont t w q ∧ Cont q stream dyadic ∧ Cont w regseq stream ∧
                        Cont q e real ∧ Cont real p row)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle endpoint pkg ∧
                        (Cont real (BHist.e0 hostTail) q → False) ∧
                          (Cont real (BHist.e1 hostTail) q → False))
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier regseqUnary wRegseqStream qStreamDyadic qEReal realEndpoint endpointPkg
  obtain ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
    cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed (unary_cont_closed qUnary eUnary qEReal) pUnary realEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint
          (And.intro
            ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary,
              cUnary, pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
            (hsame_refl endpoint))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨twq, qStreamDyadic, wRegseqStream, qEReal,
          cont_result_hsame_transport realEndpoint (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport endpointUnary (hsame_symm source.right), endpointPkg,
          (fun hostReturn =>
            cont_mutual_extension_right_tail_absurd.left qEReal hostReturn),
          (fun hostReturn =>
            cont_mutual_extension_right_tail_absurd.right qEReal hostReturn)⟩
  }

end BEDC.Derived.CauchyModulusRefinementUp
