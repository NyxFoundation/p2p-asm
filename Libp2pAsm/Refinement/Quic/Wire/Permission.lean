import Libp2pAsm.Refinement.Quic.Wire.PermissionCases0
import Libp2pAsm.Refinement.Quic.Wire.PermissionCases1
import Libp2pAsm.Refinement.Quic.Wire.PermissionCases2
import Libp2pAsm.Refinement.Quic.Wire.PermissionCases3

namespace Libp2pAsm.Refinement.Quic.Wire

/-- Exhaustive standard frame types, four levels and both sender roles,
executing the actual fetched RV64 code from a concrete zero-register state. -/
theorem permission_all_standard_inputs :
    ((List.range 31).all fun t => (List.range 4).all fun l =>
      (List.range 2).all fun r => permissionCheck t l r) = true := by
  rw [show List.range 31 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30] from by decide]
  simp only [List.all_cons, List.all_nil, Bool.and_self,
    permission_tag_0, permission_tag_1, permission_tag_2, permission_tag_3, permission_tag_4,
    permission_tag_5, permission_tag_6, permission_tag_7, permission_tag_8, permission_tag_9,
    permission_tag_10, permission_tag_11, permission_tag_12, permission_tag_13, permission_tag_14,
    permission_tag_15, permission_tag_16, permission_tag_17, permission_tag_18, permission_tag_19,
    permission_tag_20, permission_tag_21, permission_tag_22, permission_tag_23, permission_tag_24,
    permission_tag_25, permission_tag_26, permission_tag_27, permission_tag_28, permission_tag_29,
    permission_tag_30]

end Libp2pAsm.Refinement.Quic.Wire
