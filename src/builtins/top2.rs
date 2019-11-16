// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::ir2::{LBuilder, LCtxRef, LExprCell, LLoc, LMLambdaDef, LMTerm, LModule, LTerm, LTy};
use crate::mach::{MLamTerm, MVal};

use packed_simd::{shuffle, f64x2, f64x4};

use std::rc::{Rc};

pub fn build_top_level(builder: &mut LBuilder, ctx: LCtxRef) -> LModule {
  unimplemented!();
}

pub fn _include_top_level_exp(mut root: LExprCell, builder: &mut LBuilder) -> LExprCell {
  // TODO
  let sqrt_ident = builder.lookup_or_fresh_name("sqrt");
  let sqrtv4f_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::V4Flp(x0) => {
              let y = x0.sqrt();
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V4Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let sqrtv4f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      sqrtv4f_def.clone(),
      (sqrtv4f_def.mk)()
  ));
  let sqrtv4f_mx = root.append(builder, &mut |_| LTerm::MX(
      sqrtv4f_mlam.loc()
  ));
  let sqrtv4f_var = builder.fresh_var(sqrt_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      sqrt_ident.clone().into(),
      sqrtv4f_var.clone(),
      LTy::Fun(vec![LTy::V4Flp.into()], LTy::V4Flp.into()).into(),
      sqrtv4f_mx.loc(),
      root.loc()
  ));
  let sqrtv3f_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::V3Flp(x0) => {
              let y = x0.sqrt();
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V3Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let sqrtv3f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      sqrtv3f_def.clone(),
      (sqrtv3f_def.mk)()
  ));
  let sqrtv3f_mx = root.append(builder, &mut |_| LTerm::MX(
      sqrtv3f_mlam.loc()
  ));
  let sqrtv3f_var = builder.fresh_var(sqrt_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      sqrt_ident.clone().into(),
      sqrtv3f_var.clone(),
      LTy::Fun(vec![LTy::V3Flp.into()], LTy::V3Flp.into()).into(),
      sqrtv3f_mx.loc(),
      root.loc()
  ));
  let sqrtv2f_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::V2Flp(x0) => {
              let y = x0.sqrt();
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V2Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let sqrtv2f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      sqrtv2f_def.clone(),
      (sqrtv2f_def.mk)()
  ));
  let sqrtv2f_mx = root.append(builder, &mut |_| LTerm::MX(
      sqrtv2f_mlam.loc()
  ));
  let sqrtv2f_var = builder.fresh_var(sqrt_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      sqrt_ident.clone().into(),
      sqrtv2f_var.clone(),
      LTy::Fun(vec![LTy::V2Flp.into()], LTy::V2Flp.into()).into(),
      sqrtv2f_mx.loc(),
      root.loc()
  ));
  let sqrtf_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::Flp(x0) => {
              let y = x0.sqrt();
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let sqrtf_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      sqrtf_def.clone(),
      (sqrtf_def.mk)()
  ));
  let sqrtf_mx = root.append(builder, &mut |_| LTerm::MX(
      sqrtf_mlam.loc()
  ));
  let sqrtf_var = builder.fresh_var(sqrt_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      sqrt_ident.clone().into(),
      sqrtf_var.clone(),
      LTy::Fun(vec![LTy::Flp.into()], LTy::Flp.into()).into(),
      sqrtf_mx.loc(),
      root.loc()
  ));
  root = root.append(builder, &mut |_| LTerm::Alt(
      sqrt_ident.clone().into(),
      root.loc()
  ));
  let abs_ident = builder.lookup_or_fresh_name("abs");
  let absv4f_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::V4Flp(x0) => {
              let y = x0.abs();
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V4Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let absv4f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      absv4f_def.clone(),
      (absv4f_def.mk)()
  ));
  let absv4f_mx = root.append(builder, &mut |_| LTerm::MX(
      absv4f_mlam.loc()
  ));
  let absv4f_var = builder.fresh_var(abs_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      abs_ident.clone().into(),
      absv4f_var.clone(),
      LTy::Fun(vec![LTy::V4Flp.into()], LTy::V4Flp.into()).into(),
      absv4f_mx.loc(),
      root.loc()
  ));
  let absv3f_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::V3Flp(x0) => {
              let y = x0.abs();
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V3Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let absv3f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      absv3f_def.clone(),
      (absv3f_def.mk)()
  ));
  let absv3f_mx = root.append(builder, &mut |_| LTerm::MX(
      absv3f_mlam.loc()
  ));
  let absv3f_var = builder.fresh_var(abs_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      abs_ident.clone().into(),
      absv3f_var.clone(),
      LTy::Fun(vec![LTy::V3Flp.into()], LTy::V3Flp.into()).into(),
      absv3f_mx.loc(),
      root.loc()
  ));
  let absv2f_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::V2Flp(x0) => {
              let y = x0.abs();
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V2Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let absv2f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      absv2f_def.clone(),
      (absv2f_def.mk)()
  ));
  let absv2f_mx = root.append(builder, &mut |_| LTerm::MX(
      absv2f_mlam.loc()
  ));
  let absv2f_var = builder.fresh_var(abs_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      abs_ident.clone().into(),
      absv2f_var.clone(),
      LTy::Fun(vec![LTy::V2Flp.into()], LTy::V2Flp.into()).into(),
      absv2f_mx.loc(),
      root.loc()
  ));
  let absf_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::Flp(x0) => {
              let y = x0.abs();
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let absf_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      absf_def.clone(),
      (absf_def.mk)()
  ));
  let absf_mx = root.append(builder, &mut |_| LTerm::MX(
      absf_mlam.loc()
  ));
  let absf_var = builder.fresh_var(abs_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      abs_ident.clone().into(),
      absf_var.clone(),
      LTy::Fun(vec![LTy::Flp.into()], LTy::Flp.into()).into(),
      absf_mx.loc(),
      root.loc()
  ));
  root = root.append(builder, &mut |_| LTerm::Alt(
      abs_ident.clone().into(),
      root.loc()
  ));
  let cross_ident = builder.lookup_or_fresh_name("cross");
  let crossv3f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V3Flp(x0), &MVal::V3Flp(x1)) => {
              // TODO/check this: last lane should be zero-valued (invariant).
              let u: f64x4 = shuffle!(x1, [1, 2, 0, 3]);
              let v: f64x4 = shuffle!(x0, [1, 2, 0, 3]);
              let w = x0 * u - x1 * v;
              let y: f64x4 = shuffle!(w, [1, 2, 0, 3]);
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V3Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let crossv3f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      crossv3f_def.clone(),
      (crossv3f_def.mk)()
  ));
  let crossv3f_mx = root.append(builder, &mut |_| LTerm::MX(
      crossv3f_mlam.loc()
  ));
  let crossv3f_var = builder.fresh_var(cross_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      cross_ident.clone().into(),
      crossv3f_var.clone(),
      LTy::Fun(vec![LTy::V3Flp.into(), LTy::V3Flp.into()], LTy::V3Flp.into()).into(),
      crossv3f_mx.loc(),
      root.loc()
  ));
  let crossv2f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V2Flp(x0), &MVal::V2Flp(x1)) => {
              /*let mut u = [0.0, 0.0];
              let mut v = [0.0, 0.0];
              x0.write_to_slice_unaligned(&mut u);
              x1.write_to_slice_unaligned(&mut v);
              let y = u[0] * v[1] - u[1] * v[0];*/
              let u: f64x2 = shuffle!(x1, [1, 0]);
              let v: f64x2 = shuffle!(x0, [1, 0]);
              let w = x0 * u - x1 * v;
              let y: f64 = w.extract(0);
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let crossv2f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      crossv2f_def.clone(),
      (crossv2f_def.mk)()
  ));
  let crossv2f_mx = root.append(builder, &mut |_| LTerm::MX(
      crossv2f_mlam.loc()
  ));
  let crossv2f_var = builder.fresh_var(cross_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      cross_ident.clone().into(),
      crossv2f_var.clone(),
      LTy::Fun(vec![LTy::V2Flp.into(), LTy::V2Flp.into()], LTy::Flp.into()).into(),
      crossv2f_mx.loc(),
      root.loc()
  ));
  root = root.append(builder, &mut |_| LTerm::Alt(
      cross_ident.clone().into(),
      root.loc()
  ));
  let dot_ident = builder.lookup_or_fresh_name("dot");
  let dotv4f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V4Flp(x0), &MVal::V4Flp(x1)) => {
              let y = (x0 * x1).sum();
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let dotv4f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      dotv4f_def.clone(),
      (dotv4f_def.mk)()
  ));
  let dotv4f_mx = root.append(builder, &mut |_| LTerm::MX(
      dotv4f_mlam.loc()
  ));
  let dotv4f_var = builder.fresh_var(dot_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      dot_ident.clone().into(),
      dotv4f_var.clone(),
      LTy::Fun(vec![LTy::V4Flp.into(), LTy::V4Flp.into()], LTy::Flp.into()).into(),
      dotv4f_mx.loc(),
      root.loc()
  ));
  let dotv3f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V3Flp(x0), &MVal::V3Flp(x1)) => {
              // TODO/check this: last lane should be zero-valued (invariant).
              let y = (x0 * x1).sum();
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let dotv3f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      dotv3f_def.clone(),
      (dotv3f_def.mk)()
  ));
  let dotv3f_mx = root.append(builder, &mut |_| LTerm::MX(
      dotv3f_mlam.loc()
  ));
  let dotv3f_var = builder.fresh_var(dot_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      dot_ident.clone().into(),
      dotv3f_var.clone(),
      LTy::Fun(vec![LTy::V3Flp.into(), LTy::V3Flp.into()], LTy::Flp.into()).into(),
      dotv3f_mx.loc(),
      root.loc()
  ));
  let dotv2f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V2Flp(x0), &MVal::V2Flp(x1)) => {
              let y = (x0 * x1).sum();
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let dotv2f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      dotv2f_def.clone(),
      (dotv2f_def.mk)()
  ));
  let dotv2f_mx = root.append(builder, &mut |_| LTerm::MX(
      dotv2f_mlam.loc()
  ));
  let dotv2f_var = builder.fresh_var(dot_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      dot_ident.clone().into(),
      dotv2f_var.clone(),
      LTy::Fun(vec![LTy::V2Flp.into(), LTy::V2Flp.into()], LTy::Flp.into()).into(),
      dotv2f_mx.loc(),
      root.loc()
  ));
  root = root.append(builder, &mut |_| LTerm::Alt(
      dot_ident.clone().into(),
      root.loc()
  ));
  let div_ident = builder.lookup_or_fresh_name("div");
  let divv4f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V4Flp(x0), &MVal::V4Flp(x1)) => {
              let y = x0 / x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V4Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let div_ident = builder.lookup_name("div");
      let mul_ident = builder.lookup_name("mul");
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![tmp_sink_0_e.loc(), x1_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_1_nmr_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_1_e.loc(), x0_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x1_0_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let x1_1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let adj_1_dnm_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![x1_0_e.loc(), x1_1_e.loc()]
      ));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let adj_1_quo_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![adj_1_nmr_e.loc(), adj_1_dnm_e.loc()]
      ));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![adj_1_quo_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let divv4f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      divv4f_def.clone(),
      (divv4f_def.mk)()
  ));
  let divv4f_mx = root.append(builder, &mut |_| LTerm::MX(
      divv4f_mlam.loc()
  ));
  let divv4f_var = builder.fresh_var(div_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      div_ident.clone().into(),
      divv4f_var.clone(),
      LTy::Fun(vec![LTy::V4Flp.into(), LTy::V4Flp.into()], LTy::V4Flp.into()).into(),
      divv4f_mx.loc(),
      root.loc()
  ));
  let divv3f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V3Flp(x0), &MVal::V3Flp(x1)) => {
              let y = x0 / x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V3Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let div_ident = builder.lookup_name("div");
      let mul_ident = builder.lookup_name("mul");
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![tmp_sink_0_e.loc(), x1_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_1_nmr_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_1_e.loc(), x0_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x1_0_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let x1_1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let adj_1_dnm_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![x1_0_e.loc(), x1_1_e.loc()]
      ));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let adj_1_quo_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![adj_1_nmr_e.loc(), adj_1_dnm_e.loc()]
      ));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![adj_1_quo_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let divv3f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      divv3f_def.clone(),
      (divv3f_def.mk)()
  ));
  let divv3f_mx = root.append(builder, &mut |_| LTerm::MX(
      divv3f_mlam.loc()
  ));
  let divv3f_var = builder.fresh_var(div_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      div_ident.clone().into(),
      divv3f_var.clone(),
      LTy::Fun(vec![LTy::V3Flp.into(), LTy::V3Flp.into()], LTy::V3Flp.into()).into(),
      divv3f_mx.loc(),
      root.loc()
  ));
  let divv2f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V2Flp(x0), &MVal::V2Flp(x1)) => {
              let y = x0 / x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V2Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let div_ident = builder.lookup_name("div");
      let mul_ident = builder.lookup_name("mul");
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![tmp_sink_0_e.loc(), x1_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_1_nmr_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_1_e.loc(), x0_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x1_0_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let x1_1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let adj_1_dnm_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![x1_0_e.loc(), x1_1_e.loc()]
      ));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let adj_1_quo_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![adj_1_nmr_e.loc(), adj_1_dnm_e.loc()]
      ));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![adj_1_quo_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let divv2f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      divv2f_def.clone(),
      (divv2f_def.mk)()
  ));
  let divv2f_mx = root.append(builder, &mut |_| LTerm::MX(
      divv2f_mlam.loc()
  ));
  let divv2f_var = builder.fresh_var(div_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      div_ident.clone().into(),
      divv2f_var.clone(),
      LTy::Fun(vec![LTy::V2Flp.into(), LTy::V2Flp.into()], LTy::V2Flp.into()).into(),
      divv2f_mx.loc(),
      root.loc()
  ));
  let divf_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::Flp(x0), &MVal::Flp(x1)) => {
              let y = x0 / x1;
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let div_ident = builder.lookup_name("div");
      let mul_ident = builder.lookup_name("mul");
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![tmp_sink_0_e.loc(), x1_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_1_nmr_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_1_e.loc(), x0_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x1_0_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let x1_1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let adj_1_dnm_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![x1_0_e.loc(), x1_1_e.loc()]
      ));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let adj_1_quo_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![adj_1_nmr_e.loc(), adj_1_dnm_e.loc()]
      ));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![adj_1_quo_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let div_e = root.append(builder, &mut |_| LTerm::LookupIdent(div_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let divf_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      divf_def.clone(),
      (divf_def.mk)()
  ));
  let divf_mx = root.append(builder, &mut |_| LTerm::MX(
      divf_mlam.loc()
  ));
  let divf_var = builder.fresh_var(div_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      div_ident.clone().into(),
      divf_var.clone(),
      LTy::Fun(vec![LTy::Flp.into(), LTy::Flp.into()], LTy::Flp.into()).into(),
      divf_mx.loc(),
      root.loc()
  ));
  root = root.append(builder, &mut |_| LTerm::Alt(
      div_ident.clone().into(),
      root.loc()
  ));
  let mul_ident = builder.lookup_or_fresh_name("mul");
  let mulv4f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V4Flp(x0), &MVal::V4Flp(x1)) => {
              let y = x0 * x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V4Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let mul_ident = builder.lookup_name("mul");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_0_e.loc(), x1_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_1_e.loc(), x0_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let mulv4f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      mulv4f_def.clone(),
      (mulv4f_def.mk)()
  ));
  let mulv4f_mx = root.append(builder, &mut |_| LTerm::MX(
      mulv4f_mlam.loc()
  ));
  let mulv4f_var = builder.fresh_var(mul_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      mul_ident.clone().into(),
      mulv4f_var.clone(),
      LTy::Fun(vec![LTy::V4Flp.into(), LTy::V4Flp.into()], LTy::V4Flp.into()).into(),
      mulv4f_mx.loc(),
      root.loc()
  ));
  let mulv3f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V3Flp(x0), &MVal::V3Flp(x1)) => {
              let y = x0 * x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V3Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let mul_ident = builder.lookup_name("mul");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_0_e.loc(), x1_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_1_e.loc(), x0_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let mulv3f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      mulv3f_def.clone(),
      (mulv3f_def.mk)()
  ));
  let mulv3f_mx = root.append(builder, &mut |_| LTerm::MX(
      mulv3f_mlam.loc()
  ));
  let mulv3f_var = builder.fresh_var(mul_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      mul_ident.clone().into(),
      mulv3f_var.clone(),
      LTy::Fun(vec![LTy::V3Flp.into(), LTy::V3Flp.into()], LTy::V3Flp.into()).into(),
      mulv3f_mx.loc(),
      root.loc()
  ));
  let mulv2f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V2Flp(x0), &MVal::V2Flp(x1)) => {
              let y = x0 * x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V2Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let mul_ident = builder.lookup_name("mul");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_0_e.loc(), x1_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_1_e.loc(), x0_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let mulv2f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      mulv2f_def.clone(),
      (mulv2f_def.mk)()
  ));
  let mulv2f_mx = root.append(builder, &mut |_| LTerm::MX(
      mulv2f_mlam.loc()
  ));
  let mulv2f_var = builder.fresh_var(mul_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      mul_ident.clone().into(),
      mulv2f_var.clone(),
      LTy::Fun(vec![LTy::V2Flp.into(), LTy::V2Flp.into()], LTy::V2Flp.into()).into(),
      mulv2f_mx.loc(),
      root.loc()
  ));
  let mulf_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::Flp(x0), &MVal::Flp(x1)) => {
              let y = x0 * x1;
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let mul_ident = builder.lookup_name("mul");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_0_e.loc(), x1_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_1_e.loc(), x0_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupIdent(mul_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let mulf_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      mulf_def.clone(),
      (mulf_def.mk)()
  ));
  let mulf_mx = root.append(builder, &mut |_| LTerm::MX(
      mulf_mlam.loc()
  ));
  let mulf_var = builder.fresh_var(mul_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      mul_ident.clone().into(),
      mulf_var.clone(),
      LTy::Fun(vec![LTy::Flp.into(), LTy::Flp.into()], LTy::Flp.into()).into(),
      mulf_mx.loc(),
      root.loc()
  ));
  root = root.append(builder, &mut |_| LTerm::Alt(
      mul_ident.clone().into(),
      root.loc()
  ));
  let sub_ident = builder.lookup_or_fresh_name("sub");
  let subv4f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V4Flp(x0), &MVal::V4Flp(x1)) => {
              let y = x0 - x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V4Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let sub_ident = builder.lookup_name("sub");
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_0_e = tmp_sink_0_e;
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![tmp_sink_1_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let sub_e = root.append(builder, &mut |_| LTerm::LookupIdent(sub_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          sub_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let subv4f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      subv4f_def.clone(),
      (subv4f_def.mk)()
  ));
  let subv4f_mx = root.append(builder, &mut |_| LTerm::MX(
      subv4f_mlam.loc()
  ));
  let subv4f_var = builder.fresh_var(sub_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      sub_ident.clone().into(),
      subv4f_var.clone(),
      LTy::Fun(vec![LTy::V4Flp.into(), LTy::V4Flp.into()], LTy::V4Flp.into()).into(),
      subv4f_mx.loc(),
      root.loc()
  ));
  let subv3f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V3Flp(x0), &MVal::V3Flp(x1)) => {
              let y = x0 - x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V3Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let sub_ident = builder.lookup_name("sub");
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_0_e = tmp_sink_0_e;
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![tmp_sink_1_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let sub_e = root.append(builder, &mut |_| LTerm::LookupIdent(sub_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          sub_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let subv3f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      subv3f_def.clone(),
      (subv3f_def.mk)()
  ));
  let subv3f_mx = root.append(builder, &mut |_| LTerm::MX(
      subv3f_mlam.loc()
  ));
  let subv3f_var = builder.fresh_var(sub_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      sub_ident.clone().into(),
      subv3f_var.clone(),
      LTy::Fun(vec![LTy::V3Flp.into(), LTy::V3Flp.into()], LTy::V3Flp.into()).into(),
      subv3f_mx.loc(),
      root.loc()
  ));
  let subv2f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V2Flp(x0), &MVal::V2Flp(x1)) => {
              let y = x0 - x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V2Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let sub_ident = builder.lookup_name("sub");
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_0_e = tmp_sink_0_e;
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![tmp_sink_1_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let sub_e = root.append(builder, &mut |_| LTerm::LookupIdent(sub_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          sub_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let subv2f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      subv2f_def.clone(),
      (subv2f_def.mk)()
  ));
  let subv2f_mx = root.append(builder, &mut |_| LTerm::MX(
      subv2f_mlam.loc()
  ));
  let subv2f_var = builder.fresh_var(sub_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      sub_ident.clone().into(),
      subv2f_var.clone(),
      LTy::Fun(vec![LTy::V2Flp.into(), LTy::V2Flp.into()], LTy::V2Flp.into()).into(),
      subv2f_mx.loc(),
      root.loc()
  ));
  let subf_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::Flp(x0), &MVal::Flp(x1)) => {
              let y = x0 - x1;
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let sub_ident = builder.lookup_name("sub");
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_0_e = tmp_sink_0_e;
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![tmp_sink_1_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let sub_e = root.append(builder, &mut |_| LTerm::LookupIdent(sub_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          sub_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let subf_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      subf_def.clone(),
      (subf_def.mk)()
  ));
  let subf_mx = root.append(builder, &mut |_| LTerm::MX(
      subf_mlam.loc()
  ));
  let subf_var = builder.fresh_var(sub_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      sub_ident.clone().into(),
      subf_var.clone(),
      LTy::Fun(vec![LTy::Flp.into(), LTy::Flp.into()], LTy::Flp.into()).into(),
      subf_mx.loc(),
      root.loc()
  ));
  root = root.append(builder, &mut |_| LTerm::Alt(
      sub_ident.clone().into(),
      root.loc()
  ));
  let neg_ident = builder.lookup_or_fresh_name("neg");
  let negv4f_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::V4Flp(x) => {
              let y = -x;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V4Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![tmp_sink_0_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![x0_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone()],
          body_e.loc()
      )
    })),
  };
  let negv4f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      negv4f_def.clone(),
      (negv4f_def.mk)()
  ));
  let negv4f_mx = root.append(builder, &mut |_| LTerm::MX(
      negv4f_mlam.loc()
  ));
  let negv4f_var = builder.fresh_var(neg_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      neg_ident.clone(),
      negv4f_var.clone(),
      LTy::Fun(vec![LTy::V4Flp.into()], LTy::V4Flp.into()).into(),
      negv4f_mx.loc(),
      root.loc()
  ));
  let negv3f_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::V3Flp(x) => {
              let y = -x;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V3Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![tmp_sink_0_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![x0_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone()],
          body_e.loc()
      )
    })),
  };
  let negv3f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      negv3f_def.clone(),
      (negv3f_def.mk)()
  ));
  let negv3f_mx = root.append(builder, &mut |_| LTerm::MX(
      negv3f_mlam.loc()
  ));
  let negv3f_var = builder.fresh_var(neg_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      neg_ident.clone(),
      negv3f_var.clone(),
      LTy::Fun(vec![LTy::V3Flp.into()], LTy::V3Flp.into()).into(),
      negv3f_mx.loc(),
      root.loc()
  ));
  let negv2f_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::V2Flp(x) => {
              let y = -x;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V2Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![tmp_sink_0_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![x0_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone()],
          body_e.loc()
      )
    })),
  };
  let negv2f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      negv2f_def.clone(),
      (negv2f_def.mk)()
  ));
  let negv2f_mx = root.append(builder, &mut |_| LTerm::MX(
      negv2f_mlam.loc()
  ));
  let negv2f_var = builder.fresh_var(neg_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      neg_ident.clone(),
      negv2f_var.clone(),
      LTy::Fun(vec![LTy::V2Flp.into()], LTy::V2Flp.into()).into(),
      negv2f_mx.loc(),
      root.loc()
  ));
  let negf_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::Flp(x) => {
              let y = -x;
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let neg_ident = builder.lookup_name("neg");
      let x0 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![tmp_sink_0_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, adj_0_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupIdent(neg_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![x0_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone()],
          body_e.loc()
      )
    })),
  };
  let negf_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      negf_def.clone(),
      (negf_def.mk)()
  ));
  let negf_mx = root.append(builder, &mut |_| LTerm::MX(
      negf_mlam.loc()
  ));
  let negf_var = builder.fresh_var(neg_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      neg_ident.clone(),
      negf_var.clone(),
      LTy::Fun(vec![LTy::Flp.into()], LTy::Flp.into()).into(),
      negf_mx.loc(),
      root.loc()
  ));
  let negb_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match &*args[0] {
            &MVal::Bit(x) => {
              let y = !x;
              MVal::Bit(y).into()
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    None,
  };
  let negb_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      negb_def.clone(),
      (negb_def.mk)()
  ));
  let negb_mx = root.append(builder, &mut |_| LTerm::MX(
      negb_mlam.loc()
  ));
  let negb_var = builder.fresh_var(neg_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      neg_ident.clone(),
      negb_var.clone(),
      LTy::Fun(vec![LTy::Bit.into()], LTy::Bit.into()).into(),
      negb_mx.loc(),
      root.loc()
  ));
  root = root.append(builder, &mut |_| LTerm::Alt(
      neg_ident.clone(),
      root.loc()
  ));
  let add_ident = builder.lookup_or_fresh_name("add");
  let addv4f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V4Flp(x0), &MVal::V4Flp(x1)) => {
              let y = x0 + x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V4Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let add_ident = builder.lookup_name("add");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, tmp_sink_0_e.loc()),
            (1, tmp_sink_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let op_e = root.append(builder, &mut |_| LTerm::LookupIdent(add_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          op_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let addv4f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      addv4f_def.clone(),
      (addv4f_def.mk)()
  ));
  let addv4f_mx = root.append(builder, &mut |_| LTerm::MX(
      addv4f_mlam.loc()
  ));
  let addv4f_var = builder.fresh_var(add_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      add_ident.clone(),
      addv4f_var.clone(),
      LTy::Fun(vec![LTy::V4Flp.into(), LTy::V4Flp.into()], LTy::V4Flp.into()).into(),
      addv4f_mx.loc(),
      root.loc()
  ));
  let addv3f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V3Flp(x0), &MVal::V3Flp(x1)) => {
              let y = x0 + x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V3Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let add_ident = builder.lookup_name("add");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, tmp_sink_0_e.loc()),
            (1, tmp_sink_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let op_e = root.append(builder, &mut |_| LTerm::LookupIdent(add_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          op_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let addv3f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      addv3f_def.clone(),
      (addv3f_def.mk)()
  ));
  let addv3f_mx = root.append(builder, &mut |_| LTerm::MX(
      addv3f_mlam.loc()
  ));
  let addv3f_var = builder.fresh_var(add_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      add_ident.clone(),
      addv3f_var.clone(),
      LTy::Fun(vec![LTy::V3Flp.into(), LTy::V3Flp.into()], LTy::V3Flp.into()).into(),
      addv3f_mx.loc(),
      root.loc()
  ));
  let addv2f_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::V2Flp(x0), &MVal::V2Flp(x1)) => {
              let y = x0 + x1;
              if !y.is_finite().all() {
                MVal::Bot.into()
              } else {
                MVal::V2Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let add_ident = builder.lookup_name("add");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, tmp_sink_0_e.loc()),
            (1, tmp_sink_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let op_e = root.append(builder, &mut |_| LTerm::LookupIdent(add_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          op_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let addv2f_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      addv2f_def.clone(),
      (addv2f_def.mk)()
  ));
  let addv2f_mx = root.append(builder, &mut |_| LTerm::MX(
      addv2f_mlam.loc()
  ));
  let addv2f_var = builder.fresh_var(add_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      add_ident.clone(),
      addv2f_var.clone(),
      LTy::Fun(vec![LTy::V2Flp.into(), LTy::V2Flp.into()], LTy::V2Flp.into()).into(),
      addv2f_mx.loc(),
      root.loc()
  ));
  let addf_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          match (&*args[0], &*args[1]) {
            (&MVal::Flp(x0), &MVal::Flp(x1)) => {
              let y = x0 + x1;
              if !y.is_finite() {
                MVal::Bot.into()
              } else {
                MVal::Flp(y).into()
              }
            }
            _ => panic!(),
          }
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let add_ident = builder.lookup_name("add");
      let x0 = builder.fresh_anon_var();
      let x1 = builder.fresh_anon_var();
      let tmp_sink = builder.fresh_anon_var();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupVar(tmp_sink.clone()));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxRec(
          vec![
            (0, tmp_sink_0_e.loc()),
            (1, tmp_sink_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let op_e = root.append(builder, &mut |_| LTerm::LookupIdent(add_ident.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupVar(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupVar(x1.clone()));
      let pri_e = root.append(builder, &mut |_| LTerm::Apply(
          op_e.loc(),
          vec![x0_e.loc(), x1_e.loc()]
      ));
      let body_e = root.append(builder, &mut |_| LTerm::STuple(
          vec![pri_e.loc(), adj_e.loc()]
      ));
      LTerm::Lambda(
          vec![x0.clone(), x1.clone()],
          body_e.loc()
      )
    })),
  };
  let addf_mlam = root.m_append(builder, &mut |_| LMTerm::Lambda(
      addf_def.clone(),
      (addf_def.mk)()
  ));
  let addf_mx = root.append(builder, &mut |_| LTerm::MX(
      addf_mlam.loc()
  ));
  let addf_var = builder.fresh_var(add_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      add_ident.clone(),
      addf_var.clone(),
      LTy::Fun(vec![LTy::Flp.into(), LTy::Flp.into()], LTy::Flp.into()).into(),
      addf_mx.loc(),
      root.loc()
  ));
  root = root.append(builder, &mut |_| LTerm::Alt(
      add_ident.clone(),
      root.loc()
  ));
  let zero_add_ident = builder.lookup_or_fresh_name("zero_add");
  // TODO
  /*let zero_addv4f_def = root.append(builder, &mut |_| LTerm::V4FlpLit([0.0, 0.0, 0.0, 0.0]));
  let zero_addv4f_var = builder.fresh_var(zero_add_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      zero_add_ident.clone(),
      zero_addv4f_var.clone(),
      LTy::V4Flp.into(),
      zero_addv4f_def.loc(),
      root.loc()
  ));
  let zero_addv3f_def = root.append(builder, &mut |_| LTerm::V3FlpLit([0.0, 0.0, 0.0, 0.0]));
  let zero_addv3f_var = builder.fresh_var(zero_add_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      zero_add_ident.clone(),
      zero_addv3f_var.clone(),
      LTy::V3Flp.into(),
      zero_addv3f_def.loc(),
      root.loc()
  ));
  let zero_addv2f_def = root.append(builder, &mut |_| LTerm::V2FlpLit([0.0, 0.0]));
  let zero_addv2f_var = builder.fresh_var(zero_add_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      zero_add_ident.clone(),
      zero_addv2f_var.clone(),
      LTy::V2Flp.into(),
      zero_addv2f_def.loc(),
      root.loc()
  ));*/
  let zero_addf_def = root.append(builder, &mut |_| LTerm::FlpLit(0.0));
  let zero_addf_var = builder.fresh_var(zero_add_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      zero_add_ident.clone(),
      zero_addf_var.clone(),
      LTy::Flp.into(),
      zero_addf_def.loc(),
      root.loc()
  ));
  let zero_addi_def = root.append(builder, &mut |_| LTerm::IntLit(0));
  let zero_addi_var = builder.fresh_var(zero_add_ident.clone());
  root = root.append(builder, &mut |_| LTerm::LetAlt(
      zero_add_ident.clone(),
      zero_addi_var.clone(),
      LTy::Int.into(),
      zero_addi_def.loc(),
      root.loc()
  ));
  root = root.append(builder, &mut |_| LTerm::Alt(
      zero_add_ident.clone(),
      root.loc()
  ));
  root
}
