// This file and its contents are licensed by their authors and copyright holders under the Apache
// License (Version 2.0), MIT license, or Mozilla Public License (Version 2.0), at your option, and
// may not be copied, modified, or distributed except according to those terms. For copies of these
// licenses and more information, see the COPYRIGHT file in this distribution's top-level directory.

use objrs;

#[derive(Debug, Default, Copy, Clone, PartialEq)]
#[repr(transparent)]
pub struct MTLPixelFormat(usize);

// pub const MTLPixelFormatInvalid: MTLPixelFormat = MTLPixelFormat(0);
// pub const MTLPixelFormatA8Unorm: MTLPixelFormat = MTLPixelFormat(1);
// pub const MTLPixelFormatR8Unorm: MTLPixelFormat = MTLPixelFormat(10);
// pub const MTLPixelFormatR8Unorm_sRGB: MTLPixelFormat = MTLPixelFormat(11);
// pub const MTLPixelFormatR8Snorm: MTLPixelFormat = MTLPixelFormat(12);
// pub const MTLPixelFormatR8Uint: MTLPixelFormat = MTLPixelFormat(13);
// pub const MTLPixelFormatR8Sint: MTLPixelFormat = MTLPixelFormat(14);
// pub const MTLPixelFormatR16Unorm: MTLPixelFormat = MTLPixelFormat(20);
// pub const MTLPixelFormatR16Snorm: MTLPixelFormat = MTLPixelFormat(22);
// pub const MTLPixelFormatR16Uint: MTLPixelFormat = MTLPixelFormat(23);
// pub const MTLPixelFormatR16Sint: MTLPixelFormat = MTLPixelFormat(24);
// pub const MTLPixelFormatR16Float: MTLPixelFormat = MTLPixelFormat(25);
// pub const MTLPixelFormatRG8Unorm: MTLPixelFormat = MTLPixelFormat(30);
// pub const MTLPixelFormatRG8Unorm_sRGB: MTLPixelFormat = MTLPixelFormat(31);
// pub const MTLPixelFormatRG8Snorm: MTLPixelFormat = MTLPixelFormat(32);
// pub const MTLPixelFormatRG8Uint: MTLPixelFormat = MTLPixelFormat(33);
// pub const MTLPixelFormatRG8Sint: MTLPixelFormat = MTLPixelFormat(34);
// pub const MTLPixelFormatB5G6R5Unorm: MTLPixelFormat = MTLPixelFormat(40);
// pub const MTLPixelFormatA1BGR5Unorm: MTLPixelFormat = MTLPixelFormat(41);
// pub const MTLPixelFormatABGR4Unorm: MTLPixelFormat = MTLPixelFormat(42);
// pub const MTLPixelFormatBGR5A1Unorm: MTLPixelFormat = MTLPixelFormat(43);
// pub const MTLPixelFormatR32Uint: MTLPixelFormat = MTLPixelFormat(53);
// pub const MTLPixelFormatR32Sint: MTLPixelFormat = MTLPixelFormat(54);
// pub const MTLPixelFormatR32Float: MTLPixelFormat = MTLPixelFormat(55);
// pub const MTLPixelFormatRG16Unorm: MTLPixelFormat = MTLPixelFormat(60);
// pub const MTLPixelFormatRG16Snorm: MTLPixelFormat = MTLPixelFormat(62);
// pub const MTLPixelFormatRG16Uint: MTLPixelFormat = MTLPixelFormat(63);
// pub const MTLPixelFormatRG16Sint: MTLPixelFormat = MTLPixelFormat(64);
// pub const MTLPixelFormatRG16Float: MTLPixelFormat = MTLPixelFormat(65);
// pub const MTLPixelFormatRGBA8Unorm: MTLPixelFormat = MTLPixelFormat(70);
// pub const MTLPixelFormatRGBA8Unorm_sRGB: MTLPixelFormat = MTLPixelFormat(71);
// pub const MTLPixelFormatRGBA8Snorm: MTLPixelFormat = MTLPixelFormat(72);
// pub const MTLPixelFormatRGBA8Uint: MTLPixelFormat = MTLPixelFormat(73);
// pub const MTLPixelFormatRGBA8Sint: MTLPixelFormat = MTLPixelFormat(74);
// pub const MTLPixelFormatBGRA8Unorm: MTLPixelFormat = MTLPixelFormat(80);
// pub const MTLPixelFormatBGRA8Unorm_sRGB: MTLPixelFormat = MTLPixelFormat(81);
// pub const MTLPixelFormatRGB10A2Unorm: MTLPixelFormat = MTLPixelFormat(90);
// pub const MTLPixelFormatRGB10A2Uint: MTLPixelFormat = MTLPixelFormat(91);
// pub const MTLPixelFormatRG11B10Float: MTLPixelFormat = MTLPixelFormat(92);
// pub const MTLPixelFormatRGB9E5Float: MTLPixelFormat = MTLPixelFormat(93);
// pub const MTLPixelFormatBGR10A2Unorm: MTLPixelFormat = MTLPixelFormat(94);
// pub const MTLPixelFormatBGR10_XR: MTLPixelFormat = MTLPixelFormat(554);
// pub const MTLPixelFormatBGR10_XR_sRGB: MTLPixelFormat = MTLPixelFormat(555);
// pub const MTLPixelFormatRG32Uint: MTLPixelFormat = MTLPixelFormat(103);
// pub const MTLPixelFormatRG32Sint: MTLPixelFormat = MTLPixelFormat(104);
// pub const MTLPixelFormatRG32Float: MTLPixelFormat = MTLPixelFormat(105);
// pub const MTLPixelFormatRGBA16Unorm: MTLPixelFormat = MTLPixelFormat(110);
// pub const MTLPixelFormatRGBA16Snorm: MTLPixelFormat = MTLPixelFormat(112);
// pub const MTLPixelFormatRGBA16Uint: MTLPixelFormat = MTLPixelFormat(113);
// pub const MTLPixelFormatRGBA16Sint: MTLPixelFormat = MTLPixelFormat(114);
// pub const MTLPixelFormatRGBA16Float: MTLPixelFormat = MTLPixelFormat(115);
// pub const MTLPixelFormatBGRA10_XR: MTLPixelFormat = MTLPixelFormat(552);
// pub const MTLPixelFormatBGRA10_XR_sRGB: MTLPixelFormat = MTLPixelFormat(553);
// pub const MTLPixelFormatRGBA32Uint: MTLPixelFormat = MTLPixelFormat(123);
// pub const MTLPixelFormatRGBA32Sint: MTLPixelFormat = MTLPixelFormat(124);
// pub const MTLPixelFormatRGBA32Float: MTLPixelFormat = MTLPixelFormat(125);
// pub const MTLPixelFormatBC1_RGBA: MTLPixelFormat = MTLPixelFormat(130);
// pub const MTLPixelFormatBC1_RGBA_sRGB: MTLPixelFormat = MTLPixelFormat(131);
// pub const MTLPixelFormatBC2_RGBA: MTLPixelFormat = MTLPixelFormat(132);
// pub const MTLPixelFormatBC2_RGBA_sRGB: MTLPixelFormat = MTLPixelFormat(133);
// pub const MTLPixelFormatBC3_RGBA: MTLPixelFormat = MTLPixelFormat(134);
// pub const MTLPixelFormatBC3_RGBA_sRGB: MTLPixelFormat = MTLPixelFormat(135);
// pub const MTLPixelFormatBC4_RUnorm: MTLPixelFormat = MTLPixelFormat(140);
// pub const MTLPixelFormatBC4_RSnorm: MTLPixelFormat = MTLPixelFormat(141);
// pub const MTLPixelFormatBC5_RGUnorm: MTLPixelFormat = MTLPixelFormat(142);
// pub const MTLPixelFormatBC5_RGSnorm: MTLPixelFormat = MTLPixelFormat(143);
// pub const MTLPixelFormatBC6H_RGBFloat: MTLPixelFormat = MTLPixelFormat(150);
// pub const MTLPixelFormatBC6H_RGBUfloat: MTLPixelFormat = MTLPixelFormat(151);
// pub const MTLPixelFormatBC7_RGBAUnorm: MTLPixelFormat = MTLPixelFormat(152);
// pub const MTLPixelFormatBC7_RGBAUnorm_sRGB: MTLPixelFormat = MTLPixelFormat(153);
// pub const MTLPixelFormatPVRTC_RGB_2BPP: MTLPixelFormat = MTLPixelFormat(160);
// pub const MTLPixelFormatPVRTC_RGB_2BPP_sRGB: MTLPixelFormat = MTLPixelFormat(161);
// pub const MTLPixelFormatPVRTC_RGB_4BPP: MTLPixelFormat = MTLPixelFormat(162);
// pub const MTLPixelFormatPVRTC_RGB_4BPP_sRGB: MTLPixelFormat = MTLPixelFormat(163);
// pub const MTLPixelFormatPVRTC_RGBA_2BPP: MTLPixelFormat = MTLPixelFormat(164);
// pub const MTLPixelFormatPVRTC_RGBA_2BPP_sRGB: MTLPixelFormat = MTLPixelFormat(165);
// pub const MTLPixelFormatPVRTC_RGBA_4BPP: MTLPixelFormat = MTLPixelFormat(166);
// pub const MTLPixelFormatPVRTC_RGBA_4BPP_sRGB: MTLPixelFormat = MTLPixelFormat(167);
// pub const MTLPixelFormatEAC_R11Unorm: MTLPixelFormat = MTLPixelFormat(170);
// pub const MTLPixelFormatEAC_R11Snorm: MTLPixelFormat = MTLPixelFormat(172);
// pub const MTLPixelFormatEAC_RG11Unorm: MTLPixelFormat = MTLPixelFormat(174);
// pub const MTLPixelFormatEAC_RG11Snorm: MTLPixelFormat = MTLPixelFormat(176);
// pub const MTLPixelFormatEAC_RGBA8: MTLPixelFormat = MTLPixelFormat(178);
// pub const MTLPixelFormatEAC_RGBA8_sRGB: MTLPixelFormat = MTLPixelFormat(179);
// pub const MTLPixelFormatETC2_RGB8: MTLPixelFormat = MTLPixelFormat(180);
// pub const MTLPixelFormatETC2_RGB8_sRGB: MTLPixelFormat = MTLPixelFormat(181);
// pub const MTLPixelFormatETC2_RGB8A1: MTLPixelFormat = MTLPixelFormat(182);
// pub const MTLPixelFormatETC2_RGB8A1_sRGB: MTLPixelFormat = MTLPixelFormat(183);
// pub const MTLPixelFormatASTC_4x4_sRGB: MTLPixelFormat = MTLPixelFormat(186);
// pub const MTLPixelFormatASTC_5x4_sRGB: MTLPixelFormat = MTLPixelFormat(187);
// pub const MTLPixelFormatASTC_5x5_sRGB: MTLPixelFormat = MTLPixelFormat(188);
// pub const MTLPixelFormatASTC_6x5_sRGB: MTLPixelFormat = MTLPixelFormat(189);
// pub const MTLPixelFormatASTC_6x6_sRGB: MTLPixelFormat = MTLPixelFormat(190);
// pub const MTLPixelFormatASTC_8x5_sRGB: MTLPixelFormat = MTLPixelFormat(192);
// pub const MTLPixelFormatASTC_8x6_sRGB: MTLPixelFormat = MTLPixelFormat(193);
// pub const MTLPixelFormatASTC_8x8_sRGB: MTLPixelFormat = MTLPixelFormat(194);
// pub const MTLPixelFormatASTC_10x5_sRGB: MTLPixelFormat = MTLPixelFormat(195);
// pub const MTLPixelFormatASTC_10x6_sRGB: MTLPixelFormat = MTLPixelFormat(196);
// pub const MTLPixelFormatASTC_10x8_sRGB: MTLPixelFormat = MTLPixelFormat(197);
// pub const MTLPixelFormatASTC_10x10_sRGB: MTLPixelFormat = MTLPixelFormat(198);
// pub const MTLPixelFormatASTC_12x10_sRGB: MTLPixelFormat = MTLPixelFormat(199);
// pub const MTLPixelFormatASTC_12x12_sRGB: MTLPixelFormat = MTLPixelFormat(200);
// pub const MTLPixelFormatASTC_4x4_LDR: MTLPixelFormat = MTLPixelFormat(204);
// pub const MTLPixelFormatASTC_5x4_LDR: MTLPixelFormat = MTLPixelFormat(205);
// pub const MTLPixelFormatASTC_5x5_LDR: MTLPixelFormat = MTLPixelFormat(206);
// pub const MTLPixelFormatASTC_6x5_LDR: MTLPixelFormat = MTLPixelFormat(207);
// pub const MTLPixelFormatASTC_6x6_LDR: MTLPixelFormat = MTLPixelFormat(208);
// pub const MTLPixelFormatASTC_8x5_LDR: MTLPixelFormat = MTLPixelFormat(210);
// pub const MTLPixelFormatASTC_8x6_LDR: MTLPixelFormat = MTLPixelFormat(211);
// pub const MTLPixelFormatASTC_8x8_LDR: MTLPixelFormat = MTLPixelFormat(212);
// pub const MTLPixelFormatASTC_10x5_LDR: MTLPixelFormat = MTLPixelFormat(213);
// pub const MTLPixelFormatASTC_10x6_LDR: MTLPixelFormat = MTLPixelFormat(214);
// pub const MTLPixelFormatASTC_10x8_LDR: MTLPixelFormat = MTLPixelFormat(215);
// pub const MTLPixelFormatASTC_10x10_LDR: MTLPixelFormat = MTLPixelFormat(216);
// pub const MTLPixelFormatASTC_12x10_LDR: MTLPixelFormat = MTLPixelFormat(217);
// pub const MTLPixelFormatASTC_12x12_LDR: MTLPixelFormat = MTLPixelFormat(218);
// pub const MTLPixelFormatGBGR422: MTLPixelFormat = MTLPixelFormat(240);
// pub const MTLPixelFormatBGRG422: MTLPixelFormat = MTLPixelFormat(241);
// pub const MTLPixelFormatDepth16Unorm: MTLPixelFormat = MTLPixelFormat(250);
// pub const MTLPixelFormatDepth32Float: MTLPixelFormat = MTLPixelFormat(252);
// pub const MTLPixelFormatStencil8: MTLPixelFormat = MTLPixelFormat(253);
// pub const MTLPixelFormatDepth24Unorm_Stencil8: MTLPixelFormat = MTLPixelFormat(255);
// pub const MTLPixelFormatDepth32Float_Stencil8: MTLPixelFormat = MTLPixelFormat(260);
// pub const MTLPixelFormatX32_Stencil8: MTLPixelFormat = MTLPixelFormat(261);
// pub const MTLPixelFormatX24_Stencil8: MTLPixelFormat = MTLPixelFormat(262);

impl MTLPixelFormat {
  pub const INVALID: MTLPixelFormat = MTLPixelFormat(0);
  pub const A_8_UNORM: MTLPixelFormat = MTLPixelFormat(1);
  pub const R_8_UNORM: MTLPixelFormat = MTLPixelFormat(10);
  pub const R_8_UNORM_SRGB: MTLPixelFormat = MTLPixelFormat(11);
  pub const R_8_SNORM: MTLPixelFormat = MTLPixelFormat(12);
  pub const R_8_UINT: MTLPixelFormat = MTLPixelFormat(13);
  pub const R_8_SINT: MTLPixelFormat = MTLPixelFormat(14);
  pub const R_16_UNORM: MTLPixelFormat = MTLPixelFormat(20);
  pub const R_16_SNORM: MTLPixelFormat = MTLPixelFormat(22);
  pub const R_16_UINT: MTLPixelFormat = MTLPixelFormat(23);
  pub const R_16_SINT: MTLPixelFormat = MTLPixelFormat(24);
  pub const R_16_FLOAT: MTLPixelFormat = MTLPixelFormat(25);
  pub const RG_8_UNORM: MTLPixelFormat = MTLPixelFormat(30);
  pub const RG_8_UNORM_SRGB: MTLPixelFormat = MTLPixelFormat(31);
  pub const RG_8_SNORM: MTLPixelFormat = MTLPixelFormat(32);
  pub const RG_8_UINT: MTLPixelFormat = MTLPixelFormat(33);
  pub const RG_8_SINT: MTLPixelFormat = MTLPixelFormat(34);
  pub const B_5_G_6_R_5_UNORM: MTLPixelFormat = MTLPixelFormat(40);
  pub const A_1_BGR_5_UNORM: MTLPixelFormat = MTLPixelFormat(41);
  pub const ABGR_4_UNORM: MTLPixelFormat = MTLPixelFormat(42);
  pub const BGR_5_A_1_UNORM: MTLPixelFormat = MTLPixelFormat(43);
  pub const R_32_UINT: MTLPixelFormat = MTLPixelFormat(53);
  pub const R_32_SINT: MTLPixelFormat = MTLPixelFormat(54);
  pub const R_32_FLOAT: MTLPixelFormat = MTLPixelFormat(55);
  pub const RG_16_UNORM: MTLPixelFormat = MTLPixelFormat(60);
  pub const RG_16_SNORM: MTLPixelFormat = MTLPixelFormat(62);
  pub const RG_16_UINT: MTLPixelFormat = MTLPixelFormat(63);
  pub const RG_16_SINT: MTLPixelFormat = MTLPixelFormat(64);
  pub const RG_16_FLOAT: MTLPixelFormat = MTLPixelFormat(65);
  pub const RGBA_8_UNORM: MTLPixelFormat = MTLPixelFormat(70);
  pub const RGBA_8_UNORM_SRGB: MTLPixelFormat = MTLPixelFormat(71);
  pub const RGBA_8_SNORM: MTLPixelFormat = MTLPixelFormat(72);
  pub const RGBA_8_UINT: MTLPixelFormat = MTLPixelFormat(73);
  pub const RGBA_8_SINT: MTLPixelFormat = MTLPixelFormat(74);
  pub const BGRA_8_UNORM: MTLPixelFormat = MTLPixelFormat(80);
  pub const BGRA_8_UNORM_SRGB: MTLPixelFormat = MTLPixelFormat(81);
  pub const RGB_10_A_2_UNORM: MTLPixelFormat = MTLPixelFormat(90);
  pub const RGB_10_A_2_UINT: MTLPixelFormat = MTLPixelFormat(91);
  pub const RG_11_B_10_FLOAT: MTLPixelFormat = MTLPixelFormat(92);
  pub const RGB_9_E_5_FLOAT: MTLPixelFormat = MTLPixelFormat(93);
  pub const BGR_10_A_2_UNORM: MTLPixelFormat = MTLPixelFormat(94);
  pub const BGR_10_XR: MTLPixelFormat = MTLPixelFormat(554);
  pub const BGR_10_XR_SRGB: MTLPixelFormat = MTLPixelFormat(555);
  pub const RG_32_UINT: MTLPixelFormat = MTLPixelFormat(103);
  pub const RG_32_SINT: MTLPixelFormat = MTLPixelFormat(104);
  pub const RG_32_FLOAT: MTLPixelFormat = MTLPixelFormat(105);
  pub const RGBA_16_UNORM: MTLPixelFormat = MTLPixelFormat(110);
  pub const RGBA_16_SNORM: MTLPixelFormat = MTLPixelFormat(112);
  pub const RGBA_16_UINT: MTLPixelFormat = MTLPixelFormat(113);
  pub const RGBA_16_SINT: MTLPixelFormat = MTLPixelFormat(114);
  pub const RGBA_16_FLOAT: MTLPixelFormat = MTLPixelFormat(115);
  pub const BGRA_10_XR: MTLPixelFormat = MTLPixelFormat(552);
  pub const BGRA_10_XR_SRGB: MTLPixelFormat = MTLPixelFormat(553);
  pub const RGBA_32_UINT: MTLPixelFormat = MTLPixelFormat(123);
  pub const RGBA_32_SINT: MTLPixelFormat = MTLPixelFormat(124);
  pub const RGBA_32_FLOAT: MTLPixelFormat = MTLPixelFormat(125);
  pub const BC_1_RGBA: MTLPixelFormat = MTLPixelFormat(130);
  pub const BC_1_RGBA_SRGB: MTLPixelFormat = MTLPixelFormat(131);
  pub const BC_2_RGBA: MTLPixelFormat = MTLPixelFormat(132);
  pub const BC_2_RGBA_SRGB: MTLPixelFormat = MTLPixelFormat(133);
  pub const BC_3_RGBA: MTLPixelFormat = MTLPixelFormat(134);
  pub const BC_3_RGBA_SRGB: MTLPixelFormat = MTLPixelFormat(135);
  pub const BC_4_R_UNORM: MTLPixelFormat = MTLPixelFormat(140);
  pub const BC_4_R_SNORM: MTLPixelFormat = MTLPixelFormat(141);
  pub const BC_5_RG_UNORM: MTLPixelFormat = MTLPixelFormat(142);
  pub const BC_5_RG_SNORM: MTLPixelFormat = MTLPixelFormat(143);
  pub const BC_6_H_RGB_FLOAT: MTLPixelFormat = MTLPixelFormat(150);
  pub const BC_6_H_RGB_UFLOAT: MTLPixelFormat = MTLPixelFormat(151);
  pub const BC_7_RGBA_UNORM: MTLPixelFormat = MTLPixelFormat(152);
  pub const BC_7_RGBA_UNORM_SRGB: MTLPixelFormat = MTLPixelFormat(153);
  pub const PVRTC_RGB_2_BPP: MTLPixelFormat = MTLPixelFormat(160);
  pub const PVRTC_RGB_2_BPP_SRGB: MTLPixelFormat = MTLPixelFormat(161);
  pub const PVRTC_RGB_4_BPP: MTLPixelFormat = MTLPixelFormat(162);
  pub const PVRTC_RGB_4_BPP_SRGB: MTLPixelFormat = MTLPixelFormat(163);
  pub const PVRTC_RGBA_2_BPP: MTLPixelFormat = MTLPixelFormat(164);
  pub const PVRTC_RGBA_2_BPP_SRGB: MTLPixelFormat = MTLPixelFormat(165);
  pub const PVRTC_RGBA_4_BPP: MTLPixelFormat = MTLPixelFormat(166);
  pub const PVRTC_RGBA_4_BPP_SRGB: MTLPixelFormat = MTLPixelFormat(167);
  pub const EAC_R_11_UNORM: MTLPixelFormat = MTLPixelFormat(170);
  pub const EAC_R_11_SNORM: MTLPixelFormat = MTLPixelFormat(172);
  pub const EAC_RG_11_UNORM: MTLPixelFormat = MTLPixelFormat(174);
  pub const EAC_RG_11_SNORM: MTLPixelFormat = MTLPixelFormat(176);
  pub const EAC_RGBA_8: MTLPixelFormat = MTLPixelFormat(178);
  pub const EAC_RGBA_8_SRGB: MTLPixelFormat = MTLPixelFormat(179);
  pub const ETC_2_RGB_8: MTLPixelFormat = MTLPixelFormat(180);
  pub const ETC_2_RGB_8_SRGB: MTLPixelFormat = MTLPixelFormat(181);
  pub const ETC_2_RGB_8_A_1: MTLPixelFormat = MTLPixelFormat(182);
  pub const ETC_2_RGB_8_A_1_SRGB: MTLPixelFormat = MTLPixelFormat(183);
  pub const ASTC_4X4_SRGB: MTLPixelFormat = MTLPixelFormat(186);
  pub const ASTC_5X4_SRGB: MTLPixelFormat = MTLPixelFormat(187);
  pub const ASTC_5X5_SRGB: MTLPixelFormat = MTLPixelFormat(188);
  pub const ASTC_6X5_SRGB: MTLPixelFormat = MTLPixelFormat(189);
  pub const ASTC_6X6_SRGB: MTLPixelFormat = MTLPixelFormat(190);
  pub const ASTC_8X5_SRGB: MTLPixelFormat = MTLPixelFormat(192);
  pub const ASTC_8X6_SRGB: MTLPixelFormat = MTLPixelFormat(193);
  pub const ASTC_8X8_SRGB: MTLPixelFormat = MTLPixelFormat(194);
  pub const ASTC_10X5_SRGB: MTLPixelFormat = MTLPixelFormat(195);
  pub const ASTC_10X6_SRGB: MTLPixelFormat = MTLPixelFormat(196);
  pub const ASTC_10X8_SRGB: MTLPixelFormat = MTLPixelFormat(197);
  pub const ASTC_10X10_SRGB: MTLPixelFormat = MTLPixelFormat(198);
  pub const ASTC_12X10_SRGB: MTLPixelFormat = MTLPixelFormat(199);
  pub const ASTC_12X12_SRGB: MTLPixelFormat = MTLPixelFormat(200);
  pub const ASTC_4X4_LDR: MTLPixelFormat = MTLPixelFormat(204);
  pub const ASTC_5X4_LDR: MTLPixelFormat = MTLPixelFormat(205);
  pub const ASTC_5X5_LDR: MTLPixelFormat = MTLPixelFormat(206);
  pub const ASTC_6X5_LDR: MTLPixelFormat = MTLPixelFormat(207);
  pub const ASTC_6X6_LDR: MTLPixelFormat = MTLPixelFormat(208);
  pub const ASTC_8X5_LDR: MTLPixelFormat = MTLPixelFormat(210);
  pub const ASTC_8X6_LDR: MTLPixelFormat = MTLPixelFormat(211);
  pub const ASTC_8X8_LDR: MTLPixelFormat = MTLPixelFormat(212);
  pub const ASTC_10X5_LDR: MTLPixelFormat = MTLPixelFormat(213);
  pub const ASTC_10X6_LDR: MTLPixelFormat = MTLPixelFormat(214);
  pub const ASTC_10X8_LDR: MTLPixelFormat = MTLPixelFormat(215);
  pub const ASTC_10X10_LDR: MTLPixelFormat = MTLPixelFormat(216);
  pub const ASTC_12X10_LDR: MTLPixelFormat = MTLPixelFormat(217);
  pub const ASTC_12X12_LDR: MTLPixelFormat = MTLPixelFormat(218);
  pub const GBGR_422: MTLPixelFormat = MTLPixelFormat(240);
  pub const BGRG_422: MTLPixelFormat = MTLPixelFormat(241);
  pub const DEPTH_16_UNORM: MTLPixelFormat = MTLPixelFormat(250);
  pub const DEPTH_32_FLOAT: MTLPixelFormat = MTLPixelFormat(252);
  pub const STENCIL_8: MTLPixelFormat = MTLPixelFormat(253);
  pub const DEPTH_24_UNORM_STENCIL_8: MTLPixelFormat = MTLPixelFormat(255);
  pub const DEPTH_32_FLOAT_STENCIL_8: MTLPixelFormat = MTLPixelFormat(260);
  pub const X32_STENCIL_8: MTLPixelFormat = MTLPixelFormat(261);
  pub const X24_STENCIL_8: MTLPixelFormat = MTLPixelFormat(262);
}

unsafe impl objrs::marker::Zeroed for MTLPixelFormat {}
impl objrs::marker::Forgettable for MTLPixelFormat {}
