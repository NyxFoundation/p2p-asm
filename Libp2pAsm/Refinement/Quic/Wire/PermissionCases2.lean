import Libp2pAsm.Refinement.Quic.Wire.PermissionCheck

namespace Libp2pAsm.Refinement.Quic.Wire
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem permission_tag_16 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 16 l r) = true :=
  by decide +kernel

theorem permission_tag_17 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 17 l r) = true :=
  by decide +kernel

theorem permission_tag_18 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 18 l r) = true :=
  by decide +kernel

theorem permission_tag_19 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 19 l r) = true :=
  by decide +kernel

theorem permission_tag_20 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 20 l r) = true :=
  by decide +kernel

theorem permission_tag_21 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 21 l r) = true :=
  by decide +kernel

theorem permission_tag_22 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 22 l r) = true :=
  by decide +kernel

theorem permission_tag_23 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 23 l r) = true :=
  by decide +kernel

end Libp2pAsm.Refinement.Quic.Wire
