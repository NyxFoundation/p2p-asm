import Libp2pAsm.Refinement.Quic.Wire.PermissionCheck

namespace Libp2pAsm.Refinement.Quic.Wire
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem permission_tag_24 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 24 l r) = true :=
  by decide +kernel

theorem permission_tag_25 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 25 l r) = true :=
  by decide +kernel

theorem permission_tag_26 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 26 l r) = true :=
  by decide +kernel

theorem permission_tag_27 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 27 l r) = true :=
  by decide +kernel

theorem permission_tag_28 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 28 l r) = true :=
  by decide +kernel

theorem permission_tag_29 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 29 l r) = true :=
  by decide +kernel

theorem permission_tag_30 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 30 l r) = true :=
  by decide +kernel

end Libp2pAsm.Refinement.Quic.Wire
