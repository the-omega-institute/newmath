import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.CauchyKovalevskayaUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

structure CauchyKovalevskayaCarrier where
  pde : BHist
  derivative : BHist
  coefficient : BHist
  initial : BHist
  jet : BHist
  stream : BHist
  rational : BHist
  dyadic : BHist
  real : BHist
  transport : BHist
  replay : BHist
  provenance : BHist
  name : BHist
  pde_derivative_jet : Cont pde derivative jet
  coefficient_initial_stream : Cont coefficient initial stream
  rational_dyadic_real : Cont rational dyadic real
  jet_stream_replay : Cont jet stream replay
  transport_names_replay : hsame transport replay
  provenance_names_real : hsame provenance real
  name_names_jet : hsame name jet

end BEDC.Derived.CauchyKovalevskayaUp
