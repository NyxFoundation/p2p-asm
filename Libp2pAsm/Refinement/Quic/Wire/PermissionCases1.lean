import Libp2pAsm.Refinement.Quic.Wire.PermissionCheck

namespace Libp2pAsm.Refinement.Quic.Wire
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem permission_tag_8 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 8 l r) = true :=
  by decide +kernel

theorem permission_tag_9 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 9 l r) = true :=
  by decide +kernel

theorem permission_tag_10 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 10 l r) = true :=
  by decide +kernel

theorem permission_tag_11 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 11 l r) = true :=
  by decide +kernel

theorem permission_tag_12 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 12 l r) = true :=
  by decide +kernel

theorem permission_tag_13 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 13 l r) = true :=
  by decide +kernel

theorem permission_tag_14 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 14 l r) = true :=
  by decide +kernel

theorem permission_tag_15 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 15 l r) = true :=
  by decide +kernel

end Libp2pAsm.Refinement.Quic.Wire
