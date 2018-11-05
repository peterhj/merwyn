// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use plex::{lexer};

use std::rc::{Rc};

lexer! {
  fn next_token(text: 'a) -> HLToken;

  r#"[ \t\r\n]"#    => HLToken::Whitespace,
  r#"#[^\n]*"#      => HLToken::LineComment,
  r#"\([*](~(.*[*]\).*))[*]\)"# => HLToken::BlockComment,

  r#"lambda"#       => HLToken::Lambda,
  r#"λ"#            => HLToken::Lambda,
  r#"extern"#       => HLToken::Extern,
  r#"pub"#          => HLToken::Pub,
  r#"let"#          => HLToken::Let,
  r#"letrec"#       => HLToken::LetRec,
  r#"in"#           => HLToken::In,
  r#":="#           => HLToken::Assigns,
  r#"="#            => HLToken::Equals,
  r#"\\"#           => HLToken::Backslash,
  r#"\."#           => HLToken::Dot,
  r#","#            => HLToken::Comma,
  r#";"#            => HLToken::Semi,

  r#"\+"#           => HLToken::Plus,
  r#"-"#            => HLToken::Minus,
  r#"\*"#           => HLToken::Star,
  r#"/"#            => HLToken::Slash,
  r#"\("#           => HLToken::LParen,
  r#"\)"#           => HLToken::RParen,
  r#"\["#           => HLToken::LBrack,
  r#"\]"#           => HLToken::RBrack,

  r#"[0-9]+"#       => HLToken::IntLit(text.parse().unwrap()),
  r#"[0-9]+\.[0-9]*"#           => HLToken::FloatLit(text.parse().unwrap()),

  r#"[a-zA-Z_][a-zA-Z0-9_]*"#   => HLToken::Ident(text.to_owned()),

  r#"."#            => unreachable!(),
}

#[derive(Clone, PartialEq, Debug)]
pub enum HLToken {
  Whitespace,
  LineComment,
  BlockComment,
  Lambda,
  Extern,
  Pub,
  Let,
  LetRec,
  In,
  Assigns,
  Equals,
  Backslash,
  Dot,
  Comma,
  Semi,
  Plus,
  Minus,
  Star,
  Slash,
  LParen,
  RParen,
  LBrack,
  RBrack,
  IntLit(i64),
  FloatLit(f64),
  Ident(String),
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

#[derive(Clone, Debug)]
pub enum HExpr {
  Apply0(Rc<HExpr>),
  Apply1(Rc<HExpr>, Rc<HExpr>),
  ApplyN(Rc<HExpr>, Vec<Rc<HExpr>>),
  Group(Rc<HExpr>),
  Extern(Rc<HExpr>, Option<Rc<HExpr>>, Rc<HExpr>),
  Let(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  LetRec(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  Add(Rc<HExpr>, Rc<HExpr>),
  Sub(Rc<HExpr>, Rc<HExpr>),
  Mul(Rc<HExpr>, Rc<HExpr>),
  Div(Rc<HExpr>, Rc<HExpr>),
  Neg(Rc<HExpr>),
  IntLit(i64),
  FloatLit(f64),
  Ident(String),
}

impl HExpr {
  /*fn is_atom(&self) -> bool {
    match self {
      &HExpr::Apply1(..) => false,
      _ => true,
    }
  }*/
}

pub struct HParser<Toks: Iterator<Item=HLToken>> {
  toks: Toks,
  curr: Option<HLToken>,
}

impl<Toks: Iterator<Item=HLToken> + Clone> HParser<Toks> {
  pub fn new(toks: Toks) -> HParser<Toks> {
    HParser{
      toks: toks,
      curr: None,
    }
  }

  fn save(&self) -> HParser<Toks> {
    HParser{
      toks: self.toks.clone(),
      curr: self.curr.clone(),
    }
  }

  fn restore(&mut self, saved: HParser<Toks>) {
    self.toks = saved.toks;
    self.curr = saved.curr;
  }

  fn lookahead(&self) -> HParser<Toks> {
    HParser{
      toks: self.toks.clone(),
      curr: None,
    }
  }

  fn advance(&mut self) {
    self.curr = self.toks.next();
  }

  fn expect(&mut self, tok: &HLToken) {
    self.advance();
    match self.curr {
      Some(ref curr_tok) => {
        assert_eq!(curr_tok, tok);
      }
      None => panic!(),
    }
  }

  fn current_token(&mut self) -> HLToken {
    match self.curr {
      Some(ref tok) => tok.clone(),
      None => panic!(),
    }
  }

  fn lbp(&self, tok: &HLToken) -> i32 {
    // TODO
    match tok {
      &HLToken::Extern |
      &HLToken::Let |
      &HLToken::LetRec |
      &HLToken::In |
      &HLToken::Equals |
      &HLToken::Comma |
      &HLToken::Semi => 0,
      &HLToken::Plus |
      &HLToken::Minus => 500,
      &HLToken::Star |
      &HLToken::Slash => 600,
      &HLToken::RParen => 0,
      &HLToken::LBrack => 800,
      &HLToken::RBrack => 0,
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
      HLToken::Let => {
        let e1_lhs = self.expression(0, -1)?;
        self.advance();
        match self.current_token() {
          HLToken::Equals => {}
          _ => panic!(),
        }
        let e1_rhs = self.expression(0, -1)?;
        self.advance();
        match self.current_token() {
          HLToken::In | HLToken::Semi => {}
          _ => panic!(),
        }
        let e2 = self.expression(0, -1)?;
        Ok(HExpr::Let(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
      }
      HLToken::LetRec => {
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
        Ok(HExpr::LetRec(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
      }
      //HLToken::In |
      //HLToken::Equals |
      //HLToken::Semi => 0,
      HLToken::Minus => {
        let right = self.expression(700, -1)?;
        Ok(HExpr::Neg(Rc::new(right)))
      }
      HLToken::LParen => {
        let right = self.expression(0, -1)?;
        match self.current_token() {
          HLToken::RParen => {}
          _ => panic!(),
        }
        self.advance();
        //Ok(HExpr::Group(Rc::new(right)))
        Ok(right)
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
      HLToken::Plus => {
        let right = self.expression(500, -1)?;
        Ok(HExpr::Add(Rc::new(left), Rc::new(right)))
      }
      HLToken::Minus => {
        let right = self.expression(500, -1)?;
        Ok(HExpr::Sub(Rc::new(left), Rc::new(right)))
      }
      HLToken::Star => {
        let right = self.expression(600, -1)?;
        Ok(HExpr::Mul(Rc::new(left), Rc::new(right)))
      }
      HLToken::Slash => {
        let right = self.expression(600, -1)?;
        Ok(HExpr::Div(Rc::new(left), Rc::new(right)))
      }
      HLToken::LBrack => {
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
            return Ok(HExpr::Apply0(Rc::new(left)));
          }
          HLToken::Comma => panic!(),
          _ => {}
        }
        let right = self.expression(0, -1)?;
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
            return Ok(HExpr::Apply1(Rc::new(left), Rc::new(right)));
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
                  return Ok(HExpr::ApplyN(Rc::new(left), args));
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
    // TODO
    //let mut saved = self.save();
    let mut left = match self._try_atom(rbp, depth) {
      Ok(left) => {
        left
      }
      Err(_) => {
        //self.restore(saved);
        return Err(());
      }
    };
    /*loop {
      saved = self.save();
      match self._try_atom(900, depth) {
        Ok(right) => {
          left = HExpr::Apply1(Rc::new(left), Rc::new(right));
        }
        Err(_) => {
          self.restore(saved);
          break;
        }
      }
    }*/
    Ok(left)
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

  pub fn parse(&mut self) -> HExpr {
    self.advance();
    match self.expression(0, -1) {
      Ok(e) => e,
      Err(_) => panic!(),
    }
  }
}
