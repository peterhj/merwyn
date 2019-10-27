// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::ir2::{LBuilder, LCtxRef, LExprCell, LLoc, LMLambdaDef, LMTerm, LModule, LTerm};
use crate::mach::{MLamTerm, MVal};

use std::rc::{Rc};

pub fn build_top_level(builder: &mut LBuilder, ctx: LCtxRef) -> LModule {
  unimplemented!();
}

pub fn _include_top_level_exp(mut root: LExprCell, builder: &mut LBuilder) -> LExprCell {
  // TODO
  let divf_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          let y = match (&*args[0], &*args[1]) {
            (&MVal::Flp(x0), &MVal::Flp(x1)) => {
              x0 * x1
            }
            _ => panic!(),
          };
          MVal::Flp(y.into()).into()
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let div_id = builder.lookup_name("div");
      let div_var = ctx.lookup_ident(div_id);
      let mul_id = builder.lookup_name("mul");
      let mul_var = ctx.lookup_ident(mul_id);
      let neg_id = builder.lookup_name("neg");
      let neg_var = ctx.lookup_ident(neg_id);
      let x0 = builder.fresh_anon_def();
      let x1 = builder.fresh_anon_def();
      let tmp_sink = builder.fresh_anon_def();
      let x1_e = root.append(builder, &mut |_| LTerm::LookupDef(x1.clone()));
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupDef(tmp_sink.clone()));
      let div_e = root.append(builder, &mut |_| LTerm::LookupDef(div_var.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![tmp_sink_0_e.loc(), x1_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupDef(mul_var.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupDef(x0.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupDef(tmp_sink.clone()));
      let adj_1_nmr_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_1_e.loc(), x0_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupDef(mul_var.clone()));
      let x1_0_e = root.append(builder, &mut |_| LTerm::LookupDef(x1.clone()));
      let x1_1_e = root.append(builder, &mut |_| LTerm::LookupDef(x1.clone()));
      let adj_1_dnm_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![x1_0_e.loc(), x1_1_e.loc()]
      ));
      let div_e = root.append(builder, &mut |_| LTerm::LookupDef(div_var.clone()));
      let adj_1_quo_e = root.append(builder, &mut |_| LTerm::Apply(
          div_e.loc(),
          vec![adj_1_nmr_e.loc(), adj_1_dnm_e.loc()]
      ));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupDef(neg_var.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![adj_1_quo_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxs(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let div_e = root.append(builder, &mut |_| LTerm::LookupDef(div_var.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupDef(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupDef(x1.clone()));
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
  let divf_mlam = root.mappend(builder, &mut |_| LMTerm::Lambda(
      divf_def.clone(),
      (divf_def.mk)()
  ));
  let divf_mx = root.append(builder, &mut |_| LTerm::MX(
      divf_mlam.loc()
  ));
  let div_id = builder.lookup_or_fresh_name("div");
  let div_var = builder.fresh_ident_def(div_id);
  root = root.append(builder, &mut |_| LTerm::Let(
      div_var.clone(),
      divf_mx.loc(),
      root.loc()
  ));
  let mulf_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          let y = match (&*args[0], &*args[1]) {
            (&MVal::Flp(x0), &MVal::Flp(x1)) => {
              x0 * x1
            }
            _ => panic!(),
          };
          MVal::Flp(y.into()).into()
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let mul_id = builder.lookup_name("mul");
      let mul_var = ctx.lookup_ident(mul_id);
      let x0 = builder.fresh_anon_def();
      let x1 = builder.fresh_anon_def();
      let tmp_sink = builder.fresh_anon_def();
      let x0_e = root.append(builder, &mut |_| LTerm::LookupDef(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupDef(x1.clone()));
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupDef(tmp_sink.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupDef(tmp_sink.clone()));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupDef(mul_var.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_0_e.loc(), x1_e.loc()]
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupDef(mul_var.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          mul_e.loc(),
          vec![tmp_sink_1_e.loc(), x0_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxs(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let mul_e = root.append(builder, &mut |_| LTerm::LookupDef(mul_var.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupDef(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupDef(x1.clone()));
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
  let mulf_mlam = root.mappend(builder, &mut |_| LMTerm::Lambda(
      mulf_def.clone(),
      (mulf_def.mk)()
  ));
  let mulf_mx = root.append(builder, &mut |_| LTerm::MX(
      mulf_mlam.loc()
  ));
  let mul_id = builder.lookup_or_fresh_name("mul");
  let mul_var = builder.fresh_ident_def(mul_id);
  root = root.append(builder, &mut |_| LTerm::Let(
      mul_var.clone(),
      mulf_mx.loc(),
      root.loc()
  ));
  let subf_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          let y = match (&*args[0], &*args[1]) {
            (&MVal::Flp(x0), &MVal::Flp(x1)) => {
              x0 - x1
            }
            _ => panic!(),
          };
          MVal::Flp(y.into()).into()
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let sub_id = builder.lookup_name("sub");
      let sub_var = ctx.lookup_ident(sub_id);
      let neg_id = builder.lookup_name("neg");
      let neg_var = ctx.lookup_ident(neg_id);
      let x0 = builder.fresh_anon_def();
      let x1 = builder.fresh_anon_def();
      let tmp_sink = builder.fresh_anon_def();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupDef(tmp_sink.clone()));
      let adj_0_e = tmp_sink_0_e;
      let neg_e = root.append(builder, &mut |_| LTerm::LookupDef(neg_var.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupDef(tmp_sink.clone()));
      let adj_1_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![tmp_sink_1_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxs(
          vec![
            (0, adj_0_e.loc()),
            (1, adj_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let sub_e = root.append(builder, &mut |_| LTerm::LookupDef(sub_var.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupDef(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupDef(x1.clone()));
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
  let subf_mlam = root.mappend(builder, &mut |_| LMTerm::Lambda(
      subf_def.clone(),
      (subf_def.mk)()
  ));
  let subf_mx = root.append(builder, &mut |_| LTerm::MX(
      subf_mlam.loc()
  ));
  let sub_id = builder.lookup_or_fresh_name("sub");
  let sub_var = builder.fresh_ident_def(sub_id);
  root = root.append(builder, &mut |_| LTerm::Let(
      sub_var.clone(),
      subf_mx.loc(),
      root.loc()
  ));
  let negf_def = LMLambdaDef{
    ar:     1,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          let y = match &*args[0] {
            &MVal::Flp(x) => {
              -x
            }
            _ => panic!(),
          };
          MVal::Flp(y.into()).into()
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let neg_id = builder.lookup_name("neg");
      let neg_var = ctx.lookup_ident(neg_id);
      let x0 = builder.fresh_anon_def();
      let tmp_sink = builder.fresh_anon_def();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupDef(tmp_sink.clone()));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupDef(neg_var.clone()));
      let adj_0_e = root.append(builder, &mut |_| LTerm::Apply(
          neg_e.loc(),
          vec![tmp_sink_0_e.loc()]
      ));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxs(
          vec![
            (0, adj_0_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let neg_e = root.append(builder, &mut |_| LTerm::LookupDef(neg_var.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupDef(x0.clone()));
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
  let negf_mlam = root.mappend(builder, &mut |_| LMTerm::Lambda(
      negf_def.clone(),
      (negf_def.mk)()
  ));
  let negf_mx = root.append(builder, &mut |_| LTerm::MX(
      negf_mlam.loc()
  ));
  let neg_id = builder.lookup_or_fresh_name("neg");
  let neg_var = builder.fresh_ident_def(neg_id);
  root = root.append(builder, &mut |_| LTerm::Let(
      neg_var.clone(),
      negf_mx.loc(),
      root.loc()
  ));
  let addf_def = LMLambdaDef{
    ar:     2,
    mk:     Rc::new(|/*root,*/ /*builder*/| {
      MLamTerm{
        fun:    Rc::new(|args| {
          let y = match (&*args[0], &*args[1]) {
            (&MVal::Flp(x0), &MVal::Flp(x1)) => {
              x0 + x1
            }
            _ => panic!(),
          };
          MVal::Flp(y.into()).into()
        })
      }
    }),
    ty:     None,
    adj:    Some(Rc::new(|def, root, ctx, builder| {
      let add_id = builder.lookup_name("add");
      let add_var = ctx.lookup_ident(add_id);
      let x0 = builder.fresh_anon_def();
      let x1 = builder.fresh_anon_def();
      let tmp_sink = builder.fresh_anon_def();
      let tmp_sink_0_e = root.append(builder, &mut |_| LTerm::LookupDef(tmp_sink.clone()));
      let tmp_sink_1_e = root.append(builder, &mut |_| LTerm::LookupDef(tmp_sink.clone()));
      let target_e = root.append(builder, &mut |_| LTerm::EnvIdxs(
          vec![
            (0, tmp_sink_0_e.loc()),
            (1, tmp_sink_1_e.loc()),
          ]
      ));
      let adj_e = root.append(builder, &mut |_| LTerm::Lambda(
          vec![tmp_sink.clone()],
          target_e.loc()
      ));
      let op_e = root.append(builder, &mut |_| LTerm::LookupDef(add_var.clone()));
      let x0_e = root.append(builder, &mut |_| LTerm::LookupDef(x0.clone()));
      let x1_e = root.append(builder, &mut |_| LTerm::LookupDef(x1.clone()));
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
  let addf_mlam = root.mappend(builder, &mut |_| LMTerm::Lambda(
      addf_def.clone(),
      (addf_def.mk)()
  ));
  let addf_mx = root.append(builder, &mut |_| LTerm::MX(
      addf_mlam.loc()
  ));
  let add_id = builder.lookup_or_fresh_name("add");
  let add_var = builder.fresh_ident_def(add_id);
  root = root.append(builder, &mut |_| LTerm::Let(
      add_var.clone(),
      addf_mx.loc(),
      root.loc()
  ));
  root
}
