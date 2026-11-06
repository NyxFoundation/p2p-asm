import Libp2pAsm.Refinement.Quic.Wire.PermissionCheck

namespace Libp2pAsm.Refinement.Quic.Wire
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem permission_tag_0 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 0 l r) = true :=
  by decide +kernel

theorem permission_tag_1 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 1 l r) = true :=
  by decide +kernel

theorem permission_tag_2 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 2 l r) = true :=
  by decide +kernel

theorem permission_tag_3 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 3 l r) = true :=
  by decide +kernel

theorem permission_tag_4 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 4 l r) = true :=
  by decide +kernel

theorem permission_tag_5 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 5 l r) = true :=
  by decide +kernel

theorem permission_tag_6 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 6 l r) = true :=
  by decide +kernel

theorem permission_tag_7 :
    ((List.range 4).all fun l => (List.range 2).all fun r => permissionCheck 7 l r) = true :=
  by decide +kernel

end Libp2pAsm.Refinement.Quic.Wire
