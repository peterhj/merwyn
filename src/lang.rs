// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use plex::{lexer};

use std::rc::{Rc};

lexer! {
  fn next_token(text: 'a) -> HLToken;

  r#"[ \t\r\n]+"#   => HLToken::Whitespace,
  r#"#[^\n]*"#      => HLToken::LineComment,
  r#"\([*](~(.*[*]\).*))[*]\)"# => HLToken::BlockComment,

  r#"extern"#       => HLToken::Extern,
  r#"intern"#       => HLToken::Intern,
  r#"lambda"#       => HLToken::Lambda,
  r#"λ"#            => HLToken::Lambda,
  r#"adj"#          => HLToken::Adj,
  r#"dyn"#          => HLToken::Dyn,
  r#"pub"#          => HLToken::Pub,
  r#"let"#          => HLToken::Let,
  r#"alt"#          => HLToken::Alt,
  r#"rec"#          => HLToken::Rec,
  r#"rnd"#          => HLToken::Rnd,
  r#"seq"#          => HLToken::Seq,
  r#"in"#           => HLToken::In,
  r#"letmemo"#      => HLToken::LetMemo,
  r#"where"#        => HLToken::Where,
  r#"for"#          => HLToken::For,
  r#"switch"#       => HLToken::Switch,
  r#"match"#        => HLToken::Match,
  r#"break"#        => HLToken::Break,
  r#"trace"#        => HLToken::Trace,
  r#":-"#           => HLToken::If,
  r#":="#           => HLToken::Assigns,
  r#"<="#           => HLToken::LtEquals,
  r#"<"#            => HLToken::Lt,
  r#">="#           => HLToken::GtEquals,
  r#">"#            => HLToken::Gt,
  r#"/="#           => HLToken::NotEquals,
  r#"=="#           => HLToken::EqEquals,
  r#"="#            => HLToken::Equals,
  r#"\~"#           => HLToken::Tilde,
  r#"\\"#           => HLToken::Backslash,
  r#"\.\.\."#       => HLToken::Ellipsis,
  r#"\.\."#         => HLToken::DotDot,
  r#"\."#           => HLToken::Dot,
  r#","#            => HLToken::Comma,
  r#";"#            => HLToken::Semi,
  r#"::"#           => HLToken::ColonColon,
  r#":"#            => HLToken::Colon,
  r#"\|\|"#         => HLToken::BarBar,
  r#"\|"#           => HLToken::Bar,
  r#"^^"#           => HLToken::HatHat,
  r#"^"#            => HLToken::Hat,
  r#"\+\+"#         => HLToken::PlusPlus,
  r#"\+"#           => HLToken::Plus,
  r#"-:"#           => HLToken::Then,
  r#"->"#           => HLToken::RArrow,
  r#"-"#            => HLToken::Dash,
  r#"\*"#           => HLToken::Star,
  r#"/"#            => HLToken::Slash,
  r#"\("#           => HLToken::LParen,
  r#"\)"#           => HLToken::RParen,
  r#"\["#           => HLToken::LBrack,
  r#"\]"#           => HLToken::RBrack,

  r#"_"#            => HLToken::WildPat,
  r#"noret"#        => HLToken::NoRet,
  r#"nonsmooth"#    => HLToken::NonSmooth,
  r#"unit"#         => HLToken::UnitLit,
  r#"bot"#          => HLToken::BotLit,
  r#"⊥"#            => HLToken::BotLit,
  r#"tee"#          => HLToken::TeeLit,
  r#"⊤"#            => HLToken::TeeLit,

  r#"[0-9]+"#       => HLToken::IntLit(text.parse().unwrap()),
  r#"[0-9]+\.[0-9]*"#           => HLToken::FloatLit(text.parse().unwrap()),

  r#"[a-zA-Z_][a-zA-Z0-9_]*[']*"#   => HLToken::Ident(text.to_owned()),
  r#"`[a-zA-Z_][a-zA-Z0-9_]*[']*"#  => HLToken::InfixIdent(text.to_owned()),

  r#"."#            => unreachable!(),
}

#[derive(Clone, PartialEq, Debug)]
pub enum HLToken {
  Whitespace,
  LineComment,
  BlockComment,
  Extern,
  Intern,
  Lambda,
  Adj,
  Dyn,
  Pub,
  Let,
  Alt,
  Rec,
  Rnd,
  Seq,
  In,
  LetMemo,
  Where,
  For,
  Switch,
  Match,
  Break,
  Trace,
  If,
  Assigns,
  Equals,
  EqEquals,
  NotEquals,
  Gt,
  GtEquals,
  Lt,
  LtEquals,
  Tilde,
  Backslash,
  Dot,
  DotDot,
  Ellipsis,
  Comma,
  Semi,
  Colon,
  ColonColon,
  Bar,
  BarBar,
  Hat,
  HatHat,
  Plus,
  PlusPlus,
  Dash,
  Then,
  RArrow,
  Star,
  Slash,
  LParen,
  RParen,
  LBrack,
  RBrack,
  WildPat,
  NoRet,
  NonSmooth,
  UnitLit,
  BotLit,
  TeeLit,
  IntLit(i64),
  FloatLit(f64),
  Ident(String),
  InfixIdent(String),
  Eof,
}

pub struct HLSourceInfo {
  pub filename: Option<String>,
}

#[derive(Clone)]
pub struct HLexer<'src> {
  original: &'src str,
  remnant:  &'src str,
  eof:      bool,
}

impl<'src> HLexer<'src> {
  pub fn new(src: &'src str, /*srcinfo: HLSourceInfo*/) -> HLexer<'src> {
    HLexer{
      original: src,
      remnant:  src,
      eof:      false,
    }
  }
}

impl<'src> Iterator for HLexer<'src> {
  type Item = HLToken;

  fn next(&mut self) -> Option<HLToken> {
    loop {
      if self.eof {
        return None;
      }
      let tok = if let Some((tok, next_remnant)) = next_token(self.remnant) {
        self.remnant = next_remnant;
        tok
      } else {
        self.eof = true;
        HLToken::Eof
      };
      match tok {
        HLToken::Whitespace |
        HLToken::LineComment |
        HLToken::BlockComment => {
          continue;
        }
        tok => {
          return Some(tok);
        }
      }
    }
  }
}

#[derive(Clone, Default, Debug)]
pub struct HLetAttrs {
  pub pub_: bool,
  //pub alt:  bool,
  pub rec:  bool,
  pub rnd:  bool,
  pub seq:  bool,
}

#[derive(Clone, Debug)]
pub enum HExpr {
  //Extern(Rc<HExpr>, Option<Rc<HExpr>>, Rc<HExpr>),
  Intern(String, Rc<HExpr>),
  Lambda(Vec<Rc<HExpr>>, Rc<HExpr>),
  Apply(Rc<HExpr>, Vec<Rc<HExpr>>),
  Tuple(Vec<Rc<HExpr>>),
  Adj(Rc<HExpr>),
  AdjDyn(Rc<HExpr>),
  Let(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>, Option<HLetAttrs>),
  LetRand(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  LetEmpty(Rc<HExpr>, Rc<HExpr>),
  LetWhere(Rc<HExpr>, Vec<Rc<HExpr>>, Rc<HExpr>, Rc<HExpr>),
  LetIf(Rc<HExpr>, Vec<Rc<HExpr>>, Rc<HExpr>),
  LetForIf(Rc<HExpr>, Vec<Rc<HExpr>>, Vec<Rc<HExpr>>, Rc<HExpr>),
  WhereLet(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  Switch(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  ShortOr(Rc<HExpr>, Rc<HExpr>),
  ShortAnd(Rc<HExpr>, Rc<HExpr>),
  Eq(Rc<HExpr>, Rc<HExpr>),
  NotEq(Rc<HExpr>, Rc<HExpr>),
  Gt(Rc<HExpr>, Rc<HExpr>),
  GtEq(Rc<HExpr>, Rc<HExpr>),
  Lt(Rc<HExpr>, Rc<HExpr>),
  LtEq(Rc<HExpr>, Rc<HExpr>),
  Or(Rc<HExpr>, Rc<HExpr>),
  And(Rc<HExpr>, Rc<HExpr>),
  Add(Rc<HExpr>, Rc<HExpr>),
  Sub(Rc<HExpr>, Rc<HExpr>),
  Mul(Rc<HExpr>, Rc<HExpr>),
  Div(Rc<HExpr>, Rc<HExpr>),
  Infix(String, Rc<HExpr>, Rc<HExpr>),
  Neg(Rc<HExpr>),
  Cons(Rc<HExpr>, Rc<HExpr>),
  Concat(Rc<HExpr>, Rc<HExpr>),
  NoRet,
  NonSmooth,
  UnitLit,
  BotLit,
  TeeLit,
  IntLit(i64),
  FloatLit(f64),
  Ident(String),
  PathLookup(Rc<HExpr>, String),
  KeyLookup(Rc<HExpr>, String),
}

pub struct HParser<Toks: Iterator<Item=HLToken>> {
  toks: Toks,
  curr: Option<HLToken>,
  prev: Option<HLToken>,
  bt:   bool,
}

impl<Toks: Iterator<Item=HLToken> + Clone> HParser<Toks> {
  pub fn new(toks: Toks) -> HParser<Toks> {
    HParser{
      toks: toks,
      curr: None,
      prev: None,
      bt:   false,
    }
  }

  fn save(&self) -> HParser<Toks> {
    HParser{
      toks: self.toks.clone(),
      curr: self.curr.clone(),
      prev: self.prev.clone(),
      bt:   self.bt,
    }
  }

  fn restore(&mut self, saved: HParser<Toks>) {
    self.toks = saved.toks;
    self.curr = saved.curr;
    self.prev = saved.prev;
    self.bt = saved.bt;
  }

  /*fn lookahead(&self) -> HParser<Toks> {
    HParser{
      toks: self.toks.clone(),
      curr: None,
    }
  }*/

  fn backtrack(&mut self) {
    assert!(!self.bt);
    self.bt = true;
  }

  fn advance(&mut self) {
    if self.bt {
      self.bt = false;
    } else {
      self.prev = self.curr.take();
      self.curr = self.toks.next();
    }
  }

  /*fn expect(&mut self, tok: &HLToken) {
    self.advance();
    match self.curr {
      Some(ref curr_tok) => {
        assert_eq!(curr_tok, tok);
      }
      None => panic!(),
    }
  }*/

  fn current_token(&mut self) -> HLToken {
    if self.bt {
      match self.prev {
        Some(ref tok) => tok.clone(),
        None => panic!(),
      }
    } else {
      match self.curr {
        Some(ref tok) => tok.clone(),
        None => panic!(),
      }
    }
  }

  fn lbp(&self, tok: &HLToken) -> i32 {
    // TODO
    match tok {
      &HLToken::Extern |
      &HLToken::Intern |
      &HLToken::Adj |
      &HLToken::Dyn |
      &HLToken::Pub |
      &HLToken::Let |
      &HLToken::Alt |
      &HLToken::Rec |
      &HLToken::Rnd |
      &HLToken::Seq |
      &HLToken::In |
      &HLToken::Where |
      &HLToken::Switch |
      &HLToken::If |
      &HLToken::For |
      &HLToken::Equals |
      &HLToken::Tilde |
      &HLToken::Backslash |
      &HLToken::Comma |
      &HLToken::Semi |
      &HLToken::Then |
      &HLToken::Bar => 0,
      &HLToken::BarBar => 300,
      &HLToken::HatHat => 320,
      &HLToken::EqEquals |
      &HLToken::NotEquals |
      &HLToken::Gt |
      &HLToken::GtEquals |
      &HLToken::Lt |
      &HLToken::LtEquals => 400,
      //&HLToken::Bar => 460,
      &HLToken::BarBar => 460,
      &HLToken::Hat => 480,
      &HLToken::Plus |
      &HLToken::Dash => 500,
      &HLToken::Star |
      &HLToken::Slash => 520,
      &HLToken::InfixIdent(_) => 600,
      &HLToken::PlusPlus => 700,
      &HLToken::ColonColon => 720,
      &HLToken::Dot => 800,
      &HLToken::RParen => 0,
      &HLToken::LBrack => 800,
      &HLToken::RBrack => 0,
      &HLToken::NoRet |
      &HLToken::NonSmooth |
      &HLToken::UnitLit |
      &HLToken::BotLit |
      &HLToken::TeeLit |
      &HLToken::IntLit(_) |
      &HLToken::FloatLit(_) |
      &HLToken::Ident(_) => 0,
      &HLToken::Eof => 0,
      _ => unimplemented!(),
    }
  }

  fn nud(&mut self, tok: HLToken) -> Result<HExpr, ()> {
    // TODO
    match tok {
      HLToken::Extern => {
        // TODO
        unimplemented!();
      }
      HLToken::Intern => {
        // TODO
        match self.current_token() {
          HLToken::Ident(mod_name) => {
            self.advance();
            match self.current_token() {
              HLToken::In | HLToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e = self.expression(0, -1)?;
            Ok(HExpr::Intern(mod_name, Rc::new(e)))
          }
          _ => panic!(),
        }
      }
      HLToken::Adj => {
        match self.current_token() {
          HLToken::Dyn => {
            self.advance();
            let e = self.expression(0, -1)?;
            Ok(HExpr::AdjDyn(Rc::new(e)))
          }
          _ => {
            let e = self.expression(0, -1)?;
            Ok(HExpr::Adj(Rc::new(e)))
          }
        }
      }
      HLToken::Pub => {
        match self.current_token() {
          HLToken::Let => {}
          _ => panic!(),
        }
        self.expression(0, -1).map(|e| match e {
          HExpr::Let(lhs, rhs, rest, maybe_attrs) => {
            let mut attrs = maybe_attrs.unwrap_or_default();
            attrs.pub_ = true;
            HExpr::Let(lhs, rhs, rest, Some(attrs))
          }
          _ => panic!(),
        })
      }
      HLToken::Let => {
        let mut maybe_attrs: Option<HLetAttrs> = None;
        match self.current_token() {
          // TODO
          /*HLToken::Alt => {
            let mut attrs = maybe_attrs.unwrap_or_default();
            attrs.alt = true;
            maybe_attrs = Some(attrs);
            self.advance();
          }*/
          HLToken::Rec => {
            let mut attrs = maybe_attrs.unwrap_or_default();
            attrs.rec = true;
            maybe_attrs = Some(attrs);
            self.advance();
          }
          HLToken::Rnd => {
            let mut attrs = maybe_attrs.unwrap_or_default();
            attrs.rnd = true;
            maybe_attrs = Some(attrs);
            self.advance();
          }
          HLToken::Seq => {
            let mut attrs = maybe_attrs.unwrap_or_default();
            attrs.seq = true;
            maybe_attrs = Some(attrs);
            self.advance();
          }
          _ => {}
        }
        let e1_lhs = self.expression(0, -1)?;
        match self.current_token() {
          HLToken::If => {
            let mut e1_rhs = vec![];
            loop {
              self.advance();
              let e1_rhs0 = self.expression(0, -1)?;
              e1_rhs.push(Rc::new(e1_rhs0));
              match self.current_token() {
                HLToken::Comma => {
                  continue;
                }
                HLToken::In | HLToken::Semi => {
                  break;
                }
                _ => panic!(),
              }
            }
            self.advance();
            let e2 = self.expression(0, -1)?;
            Ok(HExpr::LetIf(Rc::new(e1_lhs), e1_rhs, Rc::new(e2)))
          }
          HLToken::For => {
            // TODO
            let mut e1_unknowns = vec![];
            loop {
              self.advance();
              let e1_unk0 = self.expression(0, -1)?;
              e1_unknowns.push(Rc::new(e1_unk0));
              match self.current_token() {
                HLToken::Comma => {
                  continue;
                }
                HLToken::If => {
                  break;
                }
                _ => panic!(),
              }
            }
            let mut e1_rhs = vec![];
            loop {
              self.advance();
              let e1_rhs0 = self.expression(0, -1)?;
              e1_rhs.push(Rc::new(e1_rhs0));
              match self.current_token() {
                HLToken::Comma => {
                  continue;
                }
                HLToken::In | HLToken::Semi => {
                  break;
                }
                _ => panic!(),
              }
            }
            self.advance();
            let e2 = self.expression(0, -1)?;
            Ok(HExpr::LetForIf(Rc::new(e1_lhs), e1_unknowns, e1_rhs, Rc::new(e2)))
          }
          HLToken::In | HLToken::Semi => {
            self.advance();
            let e2 = self.expression(0, -1)?;
            Ok(HExpr::LetEmpty(Rc::new(e1_lhs), Rc::new(e2)))
          }
          HLToken::Equals => {
            self.advance();
            let e1_rhs = self.expression(0, -1)?;
            match self.current_token() {
              HLToken::In | HLToken::Semi => {
                self.advance();
              }
              _ => panic!(),
            }
            let e2 = self.expression(0, -1)?;
            Ok(HExpr::Let(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2), maybe_attrs))
          }
          HLToken::Tilde => {
            self.advance();
            let e1_rhs = self.expression(0, -1)?;
            match self.current_token() {
              HLToken::In | HLToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e2 = self.expression(0, -1)?;
            Ok(HExpr::LetRand(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
          }
          HLToken::Where => {
            let mut e1_clauses = vec![];
            loop {
              self.advance();
              let e1_clause0 = self.expression(0, -1)?;
              e1_clauses.push(Rc::new(e1_clause0));
              match self.current_token() {
                HLToken::Comma => {
                  continue;
                }
                HLToken::Equals => {
                  break;
                }
                _ => panic!(),
              }
            }
            /*self.advance();
            match self.current_token() {
              HLToken::Equals => {}
              _ => panic!(),
            }*/
            self.advance();
            let e1_rhs = self.expression(0, -1)?;
            match self.current_token() {
              HLToken::In | HLToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e2 = self.expression(0, -1)?;
            Ok(HExpr::LetWhere(Rc::new(e1_lhs), e1_clauses, Rc::new(e1_rhs), Rc::new(e2)))
          }
          //_ => panic!(),
          tok => panic!("unknown token in let rhs: {:?}", tok),
        }
      }
      HLToken::Where => {
        match self.current_token() {
          HLToken::Let => {}
          _ => panic!(),
        }
        self.advance();
        let e1_lhs = self.expression(0, -1)?;
        match self.current_token() {
          HLToken::Equals => {}
          _ => panic!(),
        }
        self.advance();
        let e1_rhs = self.expression(0, -1)?;
        match self.current_token() {
          HLToken::In | HLToken::Semi => {}
          _ => panic!(),
        }
        self.advance();
        let e2 = self.expression(0, -1)?;
        Ok(HExpr::WhereLet(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
      }
      HLToken::Switch => {
        let pred_e = self.expression(0, -1)?;
        match self.current_token() {
          HLToken::Then => {}
          _ => panic!(),
        }
        self.advance();
        let top_e = self.expression(0, -1)?;
        match self.current_token() {
          HLToken::Bar => {}
          _ => panic!(),
        }
        self.advance();
        let bot_e = self.expression(0, -1)?;
        Ok(HExpr::Switch(Rc::new(pred_e), Rc::new(top_e), Rc::new(bot_e)))
      }
      HLToken::Backslash => {
        match self.current_token() {
          HLToken::Dot => {}
          HLToken::Comma => {
            // TODO
            unimplemented!();
          }
          _ => panic!(),
        }
        self.advance();
        let body = self.expression(0, -1)?;
        Ok(HExpr::Lambda(vec![], Rc::new(body)))
      }
      HLToken::Dash => {
        let right = self.expression(700, -1)?;
        Ok(HExpr::Neg(Rc::new(right)))
      }
      HLToken::LParen => {
        self.advance();
        match self.current_token() {
          HLToken::RParen => {
            self.advance();
            Ok(HExpr::UnitLit)
          }
          _ => {
            self.backtrack();
            let right = self.expression(0, -1)?;
            match self.current_token() {
              HLToken::Comma => {
                // TODO
                unimplemented!();
              }
              HLToken::RParen => {}
              _ => panic!(),
            }
            self.advance();
            Ok(right)
          }
        }
      }
      HLToken::NoRet => {
        Ok(HExpr::NoRet)
      }
      HLToken::NonSmooth => {
        Ok(HExpr::NonSmooth)
      }
      HLToken::BotLit => {
        Ok(HExpr::BotLit)
      }
      HLToken::TeeLit => {
        Ok(HExpr::TeeLit)
      }
      HLToken::IntLit(x) => {
        Ok(HExpr::IntLit(x))
      }
      HLToken::FloatLit(x) => {
        Ok(HExpr::FloatLit(x))
      }
      HLToken::Ident(name) => {
        Ok(HExpr::Ident(name))
      }
      _ => {
        Err(())
      }
    }
  }

  fn led(&mut self, tok: HLToken, left: HExpr) -> Result<HExpr, ()> {
    // TODO
    match tok {
      HLToken::Dot => {
        match self.current_token() {
          HLToken::Ident(name) => {
            self.advance();
            Ok(HExpr::PathLookup(Rc::new(left), name))
          }
          _ => panic!(),
        }
      }
      HLToken::ColonColon => {
        let right = self.expression(self.lbp(&tok) - 1, -1)?;
        Ok(HExpr::Cons(Rc::new(left), Rc::new(right)))
      }
      HLToken::PlusPlus => {
        let right = self.expression(self.lbp(&tok) - 1, -1)?;
        Ok(HExpr::Concat(Rc::new(left), Rc::new(right)))
      }
      HLToken::BarBar => {
        let right = self.expression(self.lbp(&tok) - 1, -1)?;
        Ok(HExpr::ShortOr(Rc::new(left), Rc::new(right)))
      }
      HLToken::HatHat => {
        let right = self.expression(self.lbp(&tok) - 1, -1)?;
        Ok(HExpr::ShortAnd(Rc::new(left), Rc::new(right)))
      }
      HLToken::EqEquals => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::Eq(Rc::new(left), Rc::new(right)))
      }
      HLToken::NotEquals => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::NotEq(Rc::new(left), Rc::new(right)))
      }
      HLToken::Gt => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::Gt(Rc::new(left), Rc::new(right)))
      }
      HLToken::GtEquals => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::GtEq(Rc::new(left), Rc::new(right)))
      }
      HLToken::Lt => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::Lt(Rc::new(left), Rc::new(right)))
      }
      HLToken::LtEquals => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::LtEq(Rc::new(left), Rc::new(right)))
      }
      //HLToken::Bar => {
      HLToken::BarBar => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::Or(Rc::new(left), Rc::new(right)))
      }
      HLToken::Hat => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::And(Rc::new(left), Rc::new(right)))
      }
      HLToken::Plus => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::Add(Rc::new(left), Rc::new(right)))
      }
      HLToken::Dash => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::Sub(Rc::new(left), Rc::new(right)))
      }
      HLToken::Star => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::Mul(Rc::new(left), Rc::new(right)))
      }
      HLToken::Slash => {
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::Div(Rc::new(left), Rc::new(right)))
      }
      HLToken::InfixIdent(ref infix_name) => {
        let mut name = infix_name.clone();
        name.replace_range(.. 1, "");
        let right = self.expression(self.lbp(&tok), -1)?;
        Ok(HExpr::Infix(name, Rc::new(left), Rc::new(right)))
      }
      HLToken::LBrack => {
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
            //return Ok(HExpr::Apply0(Rc::new(left)));
            return Ok(HExpr::Apply(Rc::new(left), vec![]));
          }
          HLToken::Comma => panic!(),
          _ => {}
        }
        let right = self.expression(0, -1)?;
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
            //return Ok(HExpr::Apply1(Rc::new(left), Rc::new(right)));
            return Ok(HExpr::Apply(Rc::new(left), vec![Rc::new(right)]));
          }
          HLToken::Comma => {
            let mut args = vec![Rc::new(right)];
            loop {
              self.advance();
              let right = self.expression(0, -1)?;
              args.push(Rc::new(right));
              match self.current_token() {
                HLToken::RBrack => {
                  self.advance();
                  assert!(args.len() >= 2);
                  return Ok(HExpr::Apply(Rc::new(left), args));
                }
                HLToken::Comma => {}
                _ => panic!(),
              }
            }
          }
          _ => panic!(),
        }
      }
      _ => {
        Err(())
      }
    }
  }

  fn _try_expression(&mut self, rbp: i32, depth: i32) -> Result<HExpr, ()> {
    self._try_atom(rbp, depth)
  }

  fn _try_atom(&mut self, rbp: i32, depth: i32) -> Result<HExpr, ()> {
    // TODO
    let mut t = self.current_token();
    self.advance();
    let mut left = self.nud(t)?;
    t = self.current_token();
    while rbp < self.lbp(&t) {
      self.advance();
      left = self.led(t, left)?;
      t = self.current_token();
    }
    //assert!(left.is_atom());
    Ok(left)
  }

  fn expression(&mut self, rbp: i32, depth: i32) -> Result<HExpr, ()> {
    self._try_expression(rbp, depth)
  }

  pub fn parse(mut self) -> Rc<HExpr> {
    self.advance();
    match self.expression(0, -1) {
      Ok(expr) => Rc::new(expr),
      Err(_) => panic!(),
    }
  }
}
