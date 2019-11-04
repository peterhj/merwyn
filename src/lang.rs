// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use plex::{lexer};

use std::path::{PathBuf};
use std::rc::{Rc};

lexer! {
  fn next_token(text: 'a) -> HLToken;

  r#"\n"#       => HLToken::Newline,
  r#"[ \t\r]+"# => HLToken::Whitespace,
  r#"#[^\n]*"#  => HLToken::EolComment,
  r#"\([*](~(.*[*]\).*))[*]\)"# => HLToken::MultilineComment(0),

  /*r#"d'["#      => HLToken::DMinorPrimeBrack,
  r#"d["#       => HLToken::DMinorBrack,
  r#"D'["#      => HLToken::DMajorPrimeBrack,
  r#"D["#       => HLToken::DMajorBrack,
  r#"J'["#      => HLToken::JMajorPrimeBrack,
  r#"J["#       => HLToken::JMajorBrack,*/
  r#"d'"#       => HLToken::DMinorPrime,
  r#"d"#        => HLToken::DMinor,
  r#"D'"#       => HLToken::DMajorPrime,
  r#"D"#        => HLToken::DMajor,
  r#"J'"#       => HLToken::JMajorPrime,
  r#"J"#        => HLToken::JMajor,
  r#"adj"#      => HLToken::Adj,
  r#"alt"#      => HLToken::Alt,
  //r#"alternate"#=> HLToken::Alt,
  r#"as"#       => HLToken::As,
  r#"assert"#   => HLToken::Assert,
  r#"break"#    => HLToken::Break,
  r#"const"#    => HLToken::Const,
  r#"export"#   => HLToken::Export,
  r#"def"#      => HLToken::Def,
  r#"dyn"#      => HLToken::Dyn,
  r#"end"#      => HLToken::End,
  r#"for"#      => HLToken::For,
  r#"gen"#      => HLToken::Gen,
  //r#"generic"#  => HLToken::Gen,
  r#"import"#   => HLToken::Import,
  r#"in"#       => HLToken::In,
  r#"include"#  => HLToken::Include,
  //r#"lambda"#   => HLToken::Lambda,
  r#"let"#      => HLToken::Let,
  r#"match"#    => HLToken::Match,
  r#"module"#   => HLToken::Module,
  r#"pub"#      => HLToken::Pub,
  r#"rec"#      => HLToken::Rec,
  r#"ref"#      => HLToken::Ref,
  r#"require"#  => HLToken::Require,
  r#"return"#   => HLToken::Return,
  r#"rnd"#      => HLToken::Rnd,
  r#"seq"#      => HLToken::Seq,
  r#"switch"#   => HLToken::Switch,
  r#"tng"#      => HLToken::Tng,
  r#"trace"#    => HLToken::Trace,
  r#"type"#     => HLToken::Type,
  r#"undef"#    => HLToken::Undef,
  r#"unit"#     => HLToken::Unit,
  r#"unsafe"#   => HLToken::Unsafe,
  r#"where"#    => HLToken::Where,
  r#"with"#     => HLToken::With,
  r#"λ"#        => HLToken::Lambda,
  r#"≤"#        => HLToken::LtEquals,
  r#"≥"#        => HLToken::GtEquals,
  r#":-"#       => HLToken::If,
  r#":="#       => HLToken::Assigns,
  r#"<="#       => HLToken::LtEquals,
  r#"<"#        => HLToken::Lt,
  r#">="#       => HLToken::GtEquals,
  r#">"#        => HLToken::Gt,
  r#"/="#       => HLToken::NotEquals,
  r#"==>"#      => HLToken::RDDArrow,
  r#"=>"#       => HLToken::RDArrow,
  r#"=="#       => HLToken::EqEquals,
  r#"="#        => HLToken::Equals,
  r#"\~"#       => HLToken::Tilde,
  r#"\\/"#      => HLToken::BackslashSlash,
  r#"\\"#       => HLToken::Backslash,
  r#"\.\+"#     => HLToken::DotPlus,
  r#"\.-"#      => HLToken::DotDash,
  r#"\.\*"#     => HLToken::DotStar,
  r#"\./"#      => HLToken::DotSlash,
  r#"'\["#      => HLToken::LQuoteBrack,
  //r#"\.\("#     => HLToken::LDotParen,
  //r#"\.\["#     => HLToken::LDotBrack,
  //r#"\.\{"#     => HLToken::LDotCurly,
  r#"\.\.\."#   => HLToken::Ellipsis,
  r#"\.\."#     => HLToken::DotDot,
  r#"\."#       => HLToken::Dot,
  r#","#        => HLToken::Comma,
  r#";;"#       => HLToken::SemiSemi,
  r#";"#        => HLToken::Semi,
  r#"::"#       => HLToken::ColonColon,
  r#":"#        => HLToken::Colon,
  r#"<\|"#      => HLToken::LPipe,
  r#"\|>"#      => HLToken::RPipe,
  //r#"\|\|"#     => HLToken::BarBar,
  r#"\|"#       => HLToken::Bar,
  //r#"^^"#       => HLToken::HatHat,
  //r#"^"#        => HLToken::Hat,
  r#"\+\+"#     => HLToken::PlusPlus,
  r#"\+:"#      => HLToken::PlusColon,
  r#"\+\."#     => HLToken::PlusDot,
  r#"\+"#       => HLToken::Plus,
  //r#"-:"#       => HLToken::Then,
  r#"-o"#       => HLToken::ROArrow,
  r#"->"#       => HLToken::RArrow,
  r#"-:"#       => HLToken::DashColon,
  r#"-\."#      => HLToken::DashDot,
  r#"-"#        => HLToken::Dash,
  r#"\*:"#      => HLToken::StarColon,
  r#"\*\."#     => HLToken::StarDot,
  r#"\*\*"#     => HLToken::StarStar,
  r#"\*"#       => HLToken::Star,
  r#"/\\"#      => HLToken::SlashBackslash,
  r#"/:"#       => HLToken::SlashColon,
  r#"/\."#      => HLToken::SlashDot,
  r#"/"#        => HLToken::Slash,
  r#"\(\|"#     => HLToken::LParenBar,
  r#"\("#       => HLToken::LParen,
  r#"\|\)"#     => HLToken::RParenBar,
  r#"\)"#       => HLToken::RParen,
  r#"\["#       => HLToken::LBrack,
  r#"\]"#       => HLToken::RBrack,
  r#"\{"#       => HLToken::LCurly,
  r#"\}"#       => HLToken::RCurly,
  r#"'"#        => HLToken::Quote,
  r#"\?_"#      => HLToken::StagingPlace,
  r#"\?"#       => HLToken::Antiquote,
  r#"_"#        => HLToken::Place,

  //r#"'_"#       => HLToken::PlaceTy,
  //r#"'\?"#      => HLToken::TopTy,
  r#"Quo"#      => HLToken::QuoTy,
  r#"Iota"#     => HLToken::IotaTy,
  r#"Bit"#      => HLToken::BitTy,
  r#"Oct"#      => HLToken::OctTy,
  r#"Int"#      => HLToken::IntTy,
  r#"Flp"#      => HLToken::FlpTy,
  //r#"Flp16"#    => HLToken::Flp16Ty,
  //r#"Flp32"#    => HLToken::Flp32Ty,
  //r#"Fmp"#      => HLToken::FmpTy,

  r#"iota"#     => HLToken::Iota,
  r#"tee"#      => HLToken::Tee,
  r#"bot"#      => HLToken::Bot,
  r#"truth"#    => HLToken::Truth,
  r#"false"#    => HLToken::False,

  //r#"[0-9]+\.[0-9]*[fp16]"#         => HLToken::Flp16Lit(text[ .. text.len() - 1].parse().unwrap()),
  //r#"[0-9]+\.[0-9]*[fp32]"#         => HLToken::Flp32Lit(text[ .. text.len() - 1].parse().unwrap()),
  //r#"[0-9]+\.[0-9]*[fmp]"#          => HLToken::FmpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+\.[0-9]*f"#              => HLToken::FlpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+\.[0-9]*"#               => HLToken::FlpLit(text.parse().unwrap()),
  r#"[0-9]+f"#                      => HLToken::FlpLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+n"#                      => HLToken::IntLit(text[ .. text.len() - 1].parse().unwrap()),
  r#"[0-9]+"#                       => HLToken::IntLit(text.parse().unwrap()),

  r#"[a-zA-Z_][a-zA-Z0-9_]*[']*"#   => HLToken::Ident(text.to_owned()),
  r#"`[a-zA-Z_][a-zA-Z0-9_]*[']*"#  => HLToken::InfixIdent(text.to_owned()),
  r#"^[a-zA-Z_][a-zA-Z0-9_]*[']*"#  => HLToken::PostfixIdent(text.to_owned()),
  //r#"'[a-zA-Z_][a-zA-Z0-9_]*[']*"#  => HLToken::TyvarIdent(text.to_owned()),
  r#"\?[a-zA-Z_][a-zA-Z0-9_]*[']*"# => HLToken::StagingIdent(text.to_owned()),
  r#"\?[0-9]+"#                     => HLToken::StagingIndex(text.to_owned()),
  //r#"\~[A-Za-z0-9/\+]+[=]*"#        => HLToken::CrypticIdent(text.to_owned()),
  r#"\~=[A-Za-z0-9/\+]+[=]*"#       => HLToken::CrypticIdent(text.to_owned()),
  r#"\~[a-z0-9\-\.]+:[a-z0-9\-/]+"# => HLToken::UseIdent(text.to_owned()),
  r#"\~[a-z0-9\-]+"#                => HLToken::UseIdent(text.to_owned()),

  r#"."#        => HLToken::_Eof,
}

#[derive(Clone, Debug)]
pub enum HError {
  Eof,
  Unknown,
  Reserved(String),
  Unexpected(HLToken),
  Expected(Vec<HLToken>, HLToken),
  ExpectedIntLit,
  ExpectedTypat,
  MissingMatchArms,
  NoGenericAlternative,
  Other,
}

#[derive(Clone, PartialEq, Debug)]
pub enum HLToken {
  Newline,
  Whitespace,
  EolComment,
  MultilineComment(usize),
  DMajor,
  DMajorPrime,
  DMinor,
  DMinorPrime,
  JMajor,
  JMajorPrime,
  /*DMajorBrack,
  DMajorPrimeBrack,
  DMinorBrack,
  DMinorPrimeBrack,
  JMajorBrack,
  JMajorPrimeBrack,*/
  Adj,
  Alt,
  As,
  Assert,
  Break,
  Const,
  Def,
  Dyn,
  End,
  Export,
  For,
  Gen,
  Import,
  In,
  Include,
  Let,
  Match,
  Module,
  Pub,
  Rec,
  Ref,
  Require,
  Return,
  Rnd,
  Seq,
  Switch,
  Tng,
  Trace,
  Type,
  Undef,
  Unit,
  Unsafe,
  Where,
  With,
  Lambda,
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
  BackslashSlash,
  Dot,
  DotDot,
  DotPlus,
  DotDash,
  DotStar,
  DotSlash,
  Ellipsis,
  Comma,
  Semi,
  SemiSemi,
  Colon,
  ColonColon,
  Bar,
  BarBar,
  Hat,
  HatHat,
  Plus,
  PlusDot,
  PlusColon,
  PlusPlus,
  Dash,
  DashDot,
  DashColon,
  RArrow,
  RDArrow,
  RDDArrow,
  ROArrow,
  LPipe,
  RPipe,
  Star,
  StarDot,
  StarColon,
  StarStar,
  Slash,
  SlashDot,
  SlashColon,
  SlashBackslash,
  LDotParen,
  LParenBar,
  RParenBar,
  LParen,
  RParen,
  LQuoteBrack,
  LDotBrack,
  LBrack,
  RBrack,
  LDotCurly,
  LCurly,
  RCurly,
  Quote,
  Antiquote,
  StagingPlace,
  Place,
  PlaceTy,
  TopTy,
  QuoTy,
  IotaTy,
  BitTy,
  OctTy,
  IntTy,
  FlpTy,
  Iota,
  Tee,
  Bot,
  Truth,
  False,
  IntLit(i64),
  FlpLit(f64),
  Ident(String),
  InfixIdent(String),
  PostfixIdent(String),
  //TyvarIdent(String),
  StagingIdent(String),
  StagingIndex(String),
  CrypticIdent(String),
  UseIdent(String),
  _Eof,
}

#[derive(Clone, Debug)]
pub struct HLSourceInfo<'src> {
  pub source:   &'src str,
  pub path:     Option<PathBuf>,
}

#[derive(Clone, Copy, Debug)]
pub struct HLTokenInfo {
  pub line_nr:  usize,
  pub line_pos: usize,
  pub span:     Option<(usize, usize)>,
}

#[derive(Clone, Debug)]
pub struct HLexer<'src> {
  source:   &'src str,
  remnant:  &'src str,
  offset:   usize,
  line_nr:  usize,
  line_pos: usize,
  next_pos: usize,
  eof:      bool,
}

impl<'src> HLexer<'src> {
  pub fn new(source: &'src str /*srcinfo: HLSourceInfo<'src>*/) -> HLexer<'src> {
    HLexer{
      source,
      remnant:  source,
      offset:   0,
      line_nr:  0,
      line_pos: 0,
      next_pos: 0,
      eof:      false,
    }
  }
}

impl<'src> Iterator for HLexer<'src> {
  type Item = (HLToken, HLTokenInfo);

  fn next(&mut self) -> Option<(HLToken, HLTokenInfo)> {
    loop {
      if self.eof {
        let tok_info = HLTokenInfo{
          line_nr:    self.line_nr,
          line_pos:   self.line_pos,
          //text:       None,
          span:       None,
        };
        return Some((HLToken::_Eof, tok_info));
      }
      let (tok, tok_span, tok_text) = if let Some((tok, tok_text, next_remnant)) = next_token(self.remnant) {
        let tok_start = self.offset;
        let tok_len = tok_text.len();
        let tok_span = (tok_start, tok_start + tok_len);
        self.remnant = next_remnant;
        self.offset += tok_len;
        self.line_pos = self.next_pos;
        self.next_pos += tok_len;
        (tok, Some(tok_span), Some(tok_text))
      } else {
        self.line_pos = self.next_pos;
        self.eof = true;
        (HLToken::_Eof, None, None)
      };
      match (tok, tok_span, tok_text) {
        (HLToken::Newline, _, _) => {
          self.line_nr += 1;
          self.line_pos = 0;
          self.next_pos = 0;
          continue;
        }
        (HLToken::Whitespace, _, _) |
        (HLToken::EolComment, _, _) => {
          continue;
        }
        (HLToken::MultilineComment(_), _, Some(text)) => {
          let mut eol_iter = text.rmatch_indices('\n');
          let (line_ct, line_off) = match eol_iter.next() {
            None => (0, text.len()),
            Some((last_pos, _)) => {
              (1 + eol_iter.count(), text.len() - 1 - last_pos)
            }
          };
          self.line_nr += line_ct;
          self.line_pos = line_off;
          self.next_pos = line_off;
          continue;
        }
        (HLToken::MultilineComment(_), _, None) => {
          panic!();
        }
        (tok, tok_span, _) => {
          let tok_info = HLTokenInfo{
            line_nr:    self.line_nr,
            line_pos:   self.line_pos,
            span:       tok_span,
          };
          return Some((tok, tok_info));
        }
      }
    }
  }
}

#[derive(Clone, Default, Debug)]
pub struct HLetDecorators {
  pub pub_: bool,
  pub alt:  bool,
  pub gen:  bool,
  pub rec:  bool,
  //pub rnd:  bool,
  //pub seq:  bool,
  pub ty:   Option<Rc<HExpr>>,
}

#[derive(Clone, Debug)]
pub enum HTypat {
  //Top,
  //Place,
  //Tyvar(String),
  Fun(Vec<Rc<HTypat>>, Rc<HTypat>),
  Quo,
  Iota,
  Bit,
  Oct,
  Int,
  Flp,
  Ident(String),
}

impl From<HLToken> for HTypat {
  fn from(tok: HLToken) -> HTypat {
    match tok {
      HLToken::QuoTy => HTypat::Quo,
      HLToken::IotaTy => HTypat::Iota,
      HLToken::BitTy => HTypat::Bit,
      HLToken::OctTy => HTypat::Oct,
      HLToken::IntTy => HTypat::Int,
      HLToken::FlpTy => HTypat::Flp,
      HLToken::Ident(name) => HTypat::Ident(name),
      _ => panic!(),
    }
  }
}

#[derive(Clone, Debug)]
pub struct HExprRef {
  // FIXME
  pub term: Rc<HExpr>,
  pub toks: Vec<HLTokenInfo>,
}

#[derive(Clone, Debug)]
pub enum HExpr {
  End,
  //Export(Rc<HExpr>, Option<Rc<HExpr>>, Rc<HExpr>),
  //Import(String, Rc<HExpr>),
  Break(Rc<HExpr>),
  Lambda(Vec<Rc<HExpr>>, Rc<HExpr>),
  Apply(Rc<HExpr>, Vec<Rc<HExpr>>),
  UTuple(Vec<Rc<HExpr>>),
  STuple(Vec<Rc<HExpr>>),
  //ETuple(Vec<Rc<HExpr>>),
  ETuple(Vec<String>),
  PartialD(Rc<HExpr>),
  PartialAltD(Rc<HExpr>, Rc<HExpr>),
  AdjointD(Rc<HExpr>),
  TangentD(Rc<HExpr>),
  //DirectionalD(Rc<HExpr>, Rc<HExpr>),
  Jacobian(Rc<HExpr>),
  JacobianT(Rc<HExpr>),
  Adj(Rc<HExpr>),
  Tng(Rc<HExpr>),
  AdjDyn(Rc<HExpr>),
  Const(Rc<HExpr>),
  Let(Option<HLetDecorators>, Option<Rc<HExpr>>, Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  Alt(Rc<HExpr>, Rc<HExpr>),
  LetAlt(Option<HLetDecorators>, /*Rc<HExpr>,*/ Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  //LetFun(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  //LetMatch(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  LetRand(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  LetEmpty(Rc<HExpr>, Rc<HExpr>),
  LetWhere(Rc<HExpr>, Vec<Rc<HExpr>>, Rc<HExpr>, Rc<HExpr>),
  LetIf(Rc<HExpr>, Vec<Rc<HExpr>>, Rc<HExpr>),
  LetForIf(Rc<HExpr>, Vec<Rc<HExpr>>, Vec<Rc<HExpr>>, Rc<HExpr>),
  WhereLet(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  Switch(Rc<HExpr>, Rc<HExpr>, Rc<HExpr>),
  Match(Rc<HExpr>, Vec<(Rc<HExpr>, Rc<HExpr>)>),
  Alias(Rc<HExpr>, Rc<HExpr>),
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
  Postfix(String, Rc<HExpr>),
  Neg(Rc<HExpr>),
  //Cons(Rc<HExpr>, Rc<HExpr>),
  Concat(Rc<HExpr>, Rc<HExpr>),
  Quote(Rc<HExpr>),
  Antiquote(Rc<HExpr>),
  Place,
  Typat(Rc<HTypat>),
  IotaLit,
  TeeLit,
  BotLit,
  BitLit(bool),
  IntLit(i64),
  FlpLit(f64),
  Ident(String),
  StagingIdent(String),
  StagingIndex(i64),
  CrypticIdent(String),
  UseIdent(String),
  PathIndex(Rc<HExpr>, usize),
  PathLookup(Rc<HExpr>, String),
  PathELookup(Rc<HExpr>, Rc<HExpr>),
  //KeyLookup(Rc<HExpr>, String),
  //Arrow(Rc<HExpr>, Rc<HExpr>),
}

pub struct HParser<Toks> {
  toks: Toks,
  curr: Option<(HLToken, HLTokenInfo)>,
  prev: Option<(HLToken, HLTokenInfo)>,
  bt:   bool,
}

impl<Toks: Iterator<Item=(HLToken, HLTokenInfo)> + Clone> HParser<Toks> {
  pub fn new(toks: Toks) -> HParser<Toks> {
    HParser{
      toks: toks,
      curr: None,
      prev: None,
      bt:   false,
    }
  }

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

  fn current_token_(&self) -> (HLToken, Option<HLTokenInfo>) {
    if self.bt {
      match self.prev {
        Some((ref tok, ref info)) => (tok.clone(), Some(info.clone())),
        None => (HLToken::_Eof, None),
      }
    } else {
      match self.curr {
        Some((ref tok, ref info)) => (tok.clone(), Some(info.clone())),
        None => (HLToken::_Eof, None),
      }
    }
  }

  //fn current_token(&mut self) -> (HLToken, Option<&'src str>) {
  fn current_token(&self) -> HLToken {
    if self.bt {
      match self.prev {
        //Some(ref tok) => tok.clone(),
        Some((ref tok, _)) => tok.clone(),
        None => HLToken::_Eof,
      }
    } else {
      match self.curr {
        //Some(ref tok) => tok.clone(),
        Some((ref tok, _)) => tok.clone(),
        None => HLToken::_Eof,
      }
    }
  }

  fn current_token_info(&self) -> Option<HLTokenInfo> {
    if self.bt {
      match self.prev {
        Some((_, ref info)) => Some((*info).clone()),
        None => None,
      }
    } else {
      match self.curr {
        Some((_, ref info)) => Some((*info).clone()),
        None => None,
      }
    }
  }

  fn previous_token_info(&self) -> Option<HLTokenInfo> {
    if self.bt {
      panic!();
    } else {
      match self.prev {
        Some((_, ref info)) => Some((*info).clone()),
        None => None,
      }
    }
  }

  fn dash_prefix_rbp(&self) -> i32 {
    560
  }

  fn lbp(&self, tok: &HLToken) -> i32 {
    // TODO
    match tok {
      &HLToken::End |
      &HLToken::Export |
      &HLToken::Import |
      &HLToken::Module |
      &HLToken::Include |
      &HLToken::Require |
      &HLToken::Break |
      &HLToken::Return |
      &HLToken::Trace |
      &HLToken::DMajor |
      &HLToken::DMajorPrime |
      &HLToken::DMinor |
      &HLToken::DMinorPrime |
      &HLToken::JMajor |
      &HLToken::JMajorPrime |
      &HLToken::Adj |
      &HLToken::Tng |
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
      &HLToken::Match |
      &HLToken::With |
      &HLToken::If |
      &HLToken::Lambda |
      &HLToken::For |
      &HLToken::Equals |
      &HLToken::Tilde |
      &HLToken::Backslash |
      &HLToken::Comma |
      &HLToken::SemiSemi |
      &HLToken::Semi |
      &HLToken::DashColon |
      &HLToken::RPipe |
      &HLToken::RArrow |
      &HLToken::RDArrow |
      &HLToken::Colon |
      &HLToken::Bar => 0,
      &HLToken::ColonColon => 180,
      &HLToken::PlusPlus => 200,
      &HLToken::BarBar |
      &HLToken::BackslashSlash => 300,
      &HLToken::HatHat |
      &HLToken::SlashBackslash => 320,
      &HLToken::EqEquals |
      &HLToken::NotEquals |
      &HLToken::Gt |
      &HLToken::GtEquals |
      &HLToken::Lt |
      &HLToken::LtEquals => 400,
      //&HLToken::Bar => 460,
      //&HLToken::BarBar => 460,
      //&HLToken::Hat => 480,
      &HLToken::Plus |
      &HLToken::Dash => 500,
      &HLToken::Star |
      &HLToken::Slash => 520,
      &HLToken::InfixIdent(_) => 580,
      &HLToken::PostfixIdent(_) => 600,
      &HLToken::As => 700,
      &HLToken::Dot => 800,
      //&HLToken::LParenBar => _,
      &HLToken::RParenBar => 0,
      //&HLToken::LParen => _,
      &HLToken::RParen => 0,
      &HLToken::LBrack => 900,
      &HLToken::RBrack => 0,
      //&HLToken::LDotCurly => 800,
      //&HLToken::LCurly => _,
      &HLToken::RCurly => 0,
      &HLToken::Quote => 1000,
      &HLToken::_Eof => 0,
      _ => unimplemented!(),
    }
  }

  fn nud(&mut self, tok: HLToken, info: Option<HLTokenInfo>) -> Result<HExpr, HError> {
    // TODO
    match tok {
      HLToken::_Eof => {
        Err(HError::Eof)
      }
      HLToken::End => {
        // TODO
        /*let e: HExprRef = HExprRef{
          term: HExpr::End.into(),
          toks: match info {
            None => vec![],
            Some(info) => vec![info],
          }
        };*/
        Ok(HExpr::End)
      }
      HLToken::Export => {
        // TODO
        Err(HError::Reserved("export".to_owned()))
      }
      HLToken::Import => {
        // TODO
        /*match self.current_token() {
          HLToken::Ident(mod_name) => {
            self.advance();
            match self.current_token() {
              HLToken::In | HLToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e = self.expression(0)?;
            Ok(HExpr::Import(mod_name, Rc::new(e)))
          }
          _ => panic!(),
        }*/
        Err(HError::Reserved("import".to_owned()))
      }
      HLToken::DMajor => {
        match self.current_token() {
          HLToken::LBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::LBrack], t))
        }
        let e = self.expression(0)?;
        match self.current_token() {
          /*HLToken::Semi => {
            self.advance();
            let dir_e = self.expression(0)?;
            match self.current_token() {
              HLToken::RBrack => {
                self.advance();
              }
              _ => panic!(),
            }
            return Ok(HExpr::DirectionalD(Rc::new(e), Rc::new(dir_e)));
          }*/
          HLToken::RBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RBrack], t))
        }
        Ok(HExpr::AdjointD(Rc::new(e)))
      }
      HLToken::DMajorPrime => {
        match self.current_token() {
          HLToken::LBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::LBrack], t))
        }
        let e = self.expression(0)?;
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RBrack], t))
        }
        Ok(HExpr::TangentD(Rc::new(e)))
      }
      HLToken::DMinor => {
        match self.current_token() {
          HLToken::Dot => {
            self.advance();
            let mut idents = Vec::new();
            match self.current_token() {
              HLToken::LCurly => {
                self.advance();
                match self.current_token() {
                  HLToken::RCurly => {
                    self.advance();
                  }
                  _ => {
                    loop {
                      match self.current_token() {
                        HLToken::Ident(ident) => {
                          self.advance();
                          idents.push(ident);
                        }
                        t => return Err(HError::Expected(vec![HLToken::Ident("<identifier>".to_owned())], t))
                      }
                      match self.current_token() {
                        HLToken::Comma => {
                          self.advance();
                        }
                        HLToken::RCurly => {
                          self.advance();
                          break;
                        }
                        //_ => panic!(),
                        t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RCurly], t))
                      }
                    }
                  }
                }
              }
              HLToken::Ident(ident) => {
                self.advance();
                idents.push(ident);
              }
              t => return Err(HError::Expected(vec![HLToken::LCurly, HLToken::Ident("<identifier>".to_owned())], t))
            }
            let wrt = HExpr::ETuple(idents);
            match self.current_token() {
              HLToken::LBrack => {
                self.advance();
              }
              t => return Err(HError::Expected(vec![HLToken::LBrack], t))
            }
            let e = self.expression(0)?;
            match self.current_token() {
              HLToken::RBrack => {
                self.advance();
              }
              t => return Err(HError::Expected(vec![HLToken::RBrack], t))
            }
            Ok(HExpr::PartialAltD(Rc::new(wrt), Rc::new(e)))
          }
          /*HLToken::LDotCurly => {
            self.advance();
            let mut idents = Vec::new();
            match self.current_token() {
              HLToken::RCurly => {
                self.advance();
              }
              _ => {
                loop {
                  let e = self.expression(0)?;
                  idents.push(Rc::new(e));
                  match self.current_token() {
                    HLToken::Comma => {
                      self.advance();
                    }
                    HLToken::RCurly => {
                      self.advance();
                      break;
                    }
                    //_ => panic!(),
                    t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RCurly], t))
                  }
                }
              }
            }
            let wrt = HExpr::ETuple(idents);
            match self.current_token() {
              HLToken::LBrack => {
                self.advance();
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::LBrack], t))
            }
            let e = self.expression(0)?;
            match self.current_token() {
              HLToken::RBrack => {
                self.advance();
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::RBrack], t))
            }
            Ok(HExpr::PartialAltD(Rc::new(wrt), Rc::new(e)))
          }*/
          HLToken::LBrack => {
            self.advance();
            let e = self.expression(self.lbp(&HLToken::LBrack))?;
            match self.current_token() {
              HLToken::RBrack => {
                self.advance();
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::RBrack], t))
            }
            Ok(HExpr::PartialD(Rc::new(e)))
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::Dot, HLToken::LDotCurly, HLToken::LBrack], t))
        }
      }
      /*HLToken::DMinorBrack => {
        self.advance();
        let e = self.expression(self.lbp(&HLToken::LBrack))?;
        match self.current_token() {
          HLToken::RBrack => {}
          _ => panic!(),
        }
        self.advance();
        Ok(HExpr::PartialD(Rc::new(e)))
      }*/
      HLToken::DMinorPrime => {
        Err(HError::Reserved("d'".to_owned()))
      }
      HLToken::JMajor => {
        match self.current_token() {
          HLToken::LBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::LBrack], t))
        }
        let e = self.expression(0)?;
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RBrack], t))
        }
        Ok(HExpr::Jacobian(Rc::new(e)))
      }
      HLToken::JMajorPrime => {
        match self.current_token() {
          HLToken::LBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::LBrack], t))
        }
        let e = self.expression(0)?;
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RBrack], t))
        }
        Ok(HExpr::JacobianT(Rc::new(e)))
      }
      /*HLToken::Adj => {
        match self.current_token() {
          HLToken::Dyn => {
            self.advance();
            let e = self.expression(0)?;
            Ok(HExpr::AdjDyn(Rc::new(e)))
          }
          _ => {
            let e = self.expression(0)?;
            Ok(HExpr::Adj(Rc::new(e)))
          }
        }
      }
      HLToken::Tng => {
        let e = self.expression(0)?;
        Ok(HExpr::Tng(Rc::new(e)))
      }*/
      HLToken::Const => {
        let e = self.expression(0)?;
        Ok(HExpr::Const(Rc::new(e)))
      }
      /*HLToken::Pub => {
        match self.current_token() {
          HLToken::Let => {}
          _ => panic!(),
        }
        self.expression(0).map(|e| match e {
          HExpr::Let(decos, lhs, rhs, rest) => {
            let mut decos = decos.unwrap_or_default();
            decos.pub_ = true;
            HExpr::Let(Some(decos), lhs, rhs, rest)
          }
          _ => panic!(),
        })
      }*/
      HLToken::Alt => {
        let e1 = self.expression(0)?;
        match self.current_token() {
          HLToken::In | HLToken::Semi => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::In, HLToken::Semi], t))
        }
        let e2 = self.expression(0)?;
        return Ok(HExpr::Alt(Rc::new(e1), Rc::new(e2)));
      }
      HLToken::Let => {
        let mut maybe_decos: Option<HLetDecorators> = None;
        loop {
          match self.current_token() {
            /*HLToken::Match => {
              self.advance();
              let pat_e = self.expression(0)?;
              match self.current_token() {
                HLToken::Equals => {}
                _ => panic!(),
              }
              self.advance();
              let query_e = self.expression(0)?;
              match self.current_token() {
                HLToken::In | HLToken::Semi => {}
                _ => panic!(),
              }
              self.advance();
              let rest_e = self.expression(0)?;
              return Ok(HExpr::LetMatch(Rc::new(pat_e), Rc::new(query_e), Rc::new(rest_e)));
            }*/
            HLToken::Alt => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.alt = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            HLToken::Gen => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.gen = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            HLToken::Rec => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.rec = true;
              maybe_decos = Some(decos);
              self.advance();
            }
            /*HLToken::Rnd => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.rnd = true;
              maybe_decos = Some(decos);
              self.advance();
            }*/
            /*HLToken::Seq => {
              let mut decos = maybe_decos.unwrap_or_default();
              decos.seq = true;
              maybe_decos = Some(decos);
              self.advance();
            }*/
            _ => break,
          }
        }
        let decos = maybe_decos.clone().unwrap_or_default();
        if decos.gen {
          return Err(HError::Reserved("let gen".to_owned()));
        }
        if decos.alt {
          if decos.gen {
            return Err(HError::NoGenericAlternative);
          }
          let e1_lhs = self.expression(0)?;
          match self.current_token() {
            HLToken::Colon => {
              self.advance();
            }
            //_ => panic!(),
            t => return Err(HError::Expected(vec![HLToken::Colon], t))
          }
          let ty_e = self.expression(0)?;
          let mut decos = maybe_decos.unwrap_or_default();
          decos.ty = Some(Rc::new(ty_e));
          maybe_decos = Some(decos);
          match self.current_token() {
            HLToken::Equals => {
              self.advance();
            }
            //_ => panic!(),
            t => return Err(HError::Expected(vec![HLToken::Equals], t))
          }
          let e1_rhs = self.expression(0)?;
          match self.current_token() {
            HLToken::In | HLToken::Semi => {
              self.advance();
            }
            //_ => panic!(),
            t => return Err(HError::Expected(vec![HLToken::In, HLToken::Semi], t))
          }
          let e2 = self.expression(0)?;
          return Ok(HExpr::LetAlt(maybe_decos, Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)));
        }
        let e1_lhs = self.expression(0)?;
        match self.current_token() {
          /*HLToken::If => {
            let mut e1_rhs = vec![];
            loop {
              self.advance();
              let e1_rhs0 = self.expression(0)?;
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
            let e2 = self.expression(0)?;
            Ok(HExpr::LetIf(Rc::new(e1_lhs), e1_rhs, Rc::new(e2)))
          }
          HLToken::For => {
            // TODO
            let mut e1_unknowns = vec![];
            loop {
              self.advance();
              let e1_unk0 = self.expression(0)?;
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
              let e1_rhs0 = self.expression(0)?;
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
            let e2 = self.expression(0)?;
            Ok(HExpr::LetForIf(Rc::new(e1_lhs), e1_unknowns, e1_rhs, Rc::new(e2)))
          }
          HLToken::In | HLToken::Semi => {
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetEmpty(Rc::new(e1_lhs), Rc::new(e2)))
          }*/
          HLToken::Colon => {
            // TODO
            self.advance();
            let ty_e = self.expression(0)?;
            /*let mut decos = maybe_decos.unwrap_or_default();
            decos.ty = Some(Rc::new(ty_e));
            maybe_decos = Some(decos);*/
            match self.current_token() {
              HLToken::Equals => {
                self.advance();
                let e1_rhs = self.expression(0)?;
                match self.current_token() {
                  HLToken::In | HLToken::Semi => {
                    self.advance();
                  }
                  //_ => panic!(),
                  t => return Err(HError::Expected(vec![HLToken::In, HLToken::Semi], t))
                }
                let e2 = self.expression(0)?;
                Ok(HExpr::Let(maybe_decos, Some(Rc::new(ty_e)), Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::Equals], t))
            }
          }
          HLToken::Equals => {
            self.advance();
            let e1_rhs = self.expression(0)?;
            match self.current_token() {
              HLToken::In | HLToken::Semi => {
                self.advance();
              }
              //_ => panic!(),
              t => return Err(HError::Expected(vec![HLToken::In, HLToken::Semi], t))
            }
            let e2 = self.expression(0)?;
            Ok(HExpr::Let(maybe_decos, None, Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
          }
          /*HLToken::Tilde => {
            self.advance();
            let e1_rhs = self.expression(0)?;
            match self.current_token() {
              HLToken::In | HLToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetRand(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
          }*/
          /*HLToken::Where => {
            let mut e1_clauses = vec![];
            loop {
              self.advance();
              let e1_clause0 = self.expression(0)?;
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
            let e1_rhs = self.expression(0)?;
            match self.current_token() {
              HLToken::In | HLToken::Semi => {}
              _ => panic!(),
            }
            self.advance();
            let e2 = self.expression(0)?;
            Ok(HExpr::LetWhere(Rc::new(e1_lhs), e1_clauses, Rc::new(e1_rhs), Rc::new(e2)))
          }*/
          //_ => panic!(),
          tok => panic!("unknown token in let rhs: {:?}", tok),
        }
      }
      /*HLToken::Where => {
        match self.current_token() {
          HLToken::Let => {}
          _ => panic!(),
        }
        self.advance();
        let e1_lhs = self.expression(0)?;
        match self.current_token() {
          HLToken::Equals => {}
          _ => panic!(),
        }
        self.advance();
        let e1_rhs = self.expression(0)?;
        match self.current_token() {
          HLToken::In | HLToken::Semi => {}
          _ => panic!(),
        }
        self.advance();
        let e2 = self.expression(0)?;
        Ok(HExpr::WhereLet(Rc::new(e1_lhs), Rc::new(e1_rhs), Rc::new(e2)))
      }*/
      HLToken::Switch => {
        let pred_e = self.expression(0)?;
        match self.current_token() {
          HLToken::DashColon => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::DashColon], t))
        }
        let top_e = self.expression(0)?;
        match self.current_token() {
          HLToken::Bar => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::Bar], t))
        }
        let bot_e = self.expression(0)?;
        Ok(HExpr::Switch(Rc::new(pred_e), Rc::new(top_e), Rc::new(bot_e)))
      }
      HLToken::Match => {
        let query_e = self.expression(0)?;
        match self.current_token() {
          HLToken::With => {
            self.advance();
          }
          t => return Err(HError::Expected(vec![HLToken::With], t))
        }
        let mut pat_arms = vec![];
        loop {
          match self.current_token() {
            HLToken::Bar => {
              self.advance();
            }
            _ => break,
          }
          let pat_e = self.expression(0)?;
          match self.current_token() {
            HLToken::RDArrow => {
              self.advance();
            }
            t => return Err(HError::Expected(vec![HLToken::RDArrow], t))
          }
          let arm_e = self.expression(0)?;
          pat_arms.push((Rc::new(pat_e), Rc::new(arm_e)));
        }
        if pat_arms.is_empty() {
          return Err(HError::MissingMatchArms);
        }
        Ok(HExpr::Match(Rc::new(query_e), pat_arms))
      }
      HLToken::Lambda |
      HLToken::Backslash => {
        let mut params = vec![];
        match self.current_token() {
          HLToken::RArrow => {
            self.advance();
          }
          HLToken::Place | HLToken::Ident(_) => {
            loop {
              match self.current_token() {
                HLToken::Place => {
                  self.advance();
                  params.push(Rc::new(HExpr::Place));
                }
                HLToken::Ident(param_name) => {
                  self.advance();
                  params.push(Rc::new(HExpr::Ident(param_name)));
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::Place, HLToken::Ident("<identifier>".into())], t))
              }
              match self.current_token() {
                HLToken::Comma => {
                  self.advance();
                }
                HLToken::RArrow => {
                  self.advance();
                  break;
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RArrow], t))
              }
            }
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RArrow, HLToken::Place, HLToken::Ident("<identifier>".into())], t))
        }
        let body = self.expression(0)?;
        Ok(HExpr::Lambda(params, Rc::new(body)))
      }
      HLToken::Dash => {
        let right = self.expression(self.dash_prefix_rbp())?;
        Ok(HExpr::Neg(Rc::new(right)))
      }
      HLToken::LBrack => {
        let mut arg_typats = Vec::new();
        loop {
          let arg_tok = self.current_token();
          match &arg_tok {
            &HLToken::LBrack => {
              let arg_e = self.expression(0)?;
              match arg_e {
                HExpr::Typat(arg_ty) => match &*arg_ty {
                  &HTypat::Fun(..) => {
                    arg_typats.push(arg_ty);
                  }
                  _ => panic!(),
                },
                _ => return Err(HError::ExpectedTypat)
              }
            }
            &HLToken::RBrack => {
              self.advance();
              break;
            }
            &HLToken::QuoTy |
            &HLToken::IotaTy |
            &HLToken::BitTy |
            &HLToken::OctTy |
            &HLToken::IntTy |
            &HLToken::FlpTy |
            &HLToken::Ident(_) => {
              self.advance();
              arg_typats.push(HTypat::from(arg_tok).into());
              match self.current_token() {
                HLToken::Comma => {
                  self.advance();
                  continue;
                }
                HLToken::RBrack => {
                  self.advance();
                  break;
                }
                t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RBrack], t))
              }
            }
            //_ => panic!("TRACE: not a type pattern: {:?}", arg_tok),
            _ => return Err(HError::Expected(vec![
                HLToken::LBrack,
                HLToken::RBrack,
                HLToken::QuoTy,
                HLToken::IotaTy,
                HLToken::BitTy,
                HLToken::OctTy,
                HLToken::IntTy,
                HLToken::FlpTy,
                HLToken::Ident("<identifier>".into()),
                //HLToken::TyvarIdent("<type-variable>".into()),
            ], tok))
          }
        }
        match self.current_token() {
          HLToken::RArrow => {
            self.advance();
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RArrow], t))
        }
        let ret_tok = self.current_token();
        let ret_typat = match &ret_tok {
          &HLToken::LBrack => {
            let ret_e = self.expression(0)?;
            match ret_e {
              HExpr::Typat(ret_ty) => match &*ret_ty {
                &HTypat::Fun(..) => ret_ty,
                _ => panic!(),
              },
              _ => return Err(HError::ExpectedTypat)
            }
          }
          &HLToken::QuoTy |
          &HLToken::IotaTy |
          &HLToken::BitTy |
          &HLToken::OctTy |
          &HLToken::IntTy |
          &HLToken::FlpTy |
          &HLToken::Ident(_) => {
            self.advance();
            HTypat::from(ret_tok).into()
          }
          //_ => panic!(),
          _ => return Err(HError::Expected(vec![
              HLToken::LBrack,
              HLToken::QuoTy,
              HLToken::IotaTy,
              HLToken::BitTy,
              HLToken::OctTy,
              HLToken::IntTy,
              HLToken::FlpTy,
              HLToken::Ident("<identifier>".into()),
              //HLToken::TyvarIdent("<type-variable>".into()),
          ], tok))
        };
        Ok(HExpr::Typat(HTypat::Fun(arg_typats, ret_typat).into()))
      }
      HLToken::LParenBar => {
        let mut elems = Vec::new();
        match self.current_token() {
          HLToken::RParenBar => {
            self.advance();
            return Ok(HExpr::UTuple(elems));
          }
          _ => {
            loop {
              let right = self.expression(0)?;
              elems.push(Rc::new(right));
              match self.current_token() {
                HLToken::Comma => {
                  self.advance();
                }
                HLToken::RParenBar => {
                  self.advance();
                  return Ok(HExpr::UTuple(elems));
                }
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RParenBar], t))
              }
            }
          }
        }
      }
      HLToken::LParen => {
        match self.current_token() {
          HLToken::RParen => {
            self.advance();
            Ok(HExpr::STuple(Vec::new()))
          }
          _ => {
            let right = self.expression(0)?;
            match self.current_token() {
              HLToken::Comma => {
                let mut elems = vec![Rc::new(right)];
                loop {
                  match self.current_token() {
                    HLToken::Comma => {
                      self.advance();
                    }
                    HLToken::RParen => {
                      self.advance();
                      assert!(elems.len() >= 2);
                      return Ok(HExpr::STuple(elems));
                    }
                    t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RParen], t))
                  }
                  match self.current_token() {
                    HLToken::Comma => return Err(HError::Unexpected(HLToken::Comma)),
                    HLToken::RParen => {
                      self.advance();
                      return Ok(HExpr::STuple(elems));
                    }
                    _ => {}
                  }
                  let right = self.expression(0)?;
                  elems.push(Rc::new(right));
                }
              }
              HLToken::RParen => {
                self.advance();
              }
              t => return Err(HError::Expected(vec![HLToken::Comma, HLToken::RParen], t))
            }
            Ok(right)
          }
        }
      }
      HLToken::Quote => {
        let e = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Quote(e.into()))
      }
      HLToken::Antiquote => {
        match self.current_token() {
          HLToken::LParen => {
            self.advance();
          }
          t => return Err(HError::Expected(vec![HLToken::LParen], t))
        }
        let e = self.expression(0)?;
        match self.current_token() {
          HLToken::RParen => {
            self.advance();
          }
          t => return Err(HError::Expected(vec![HLToken::RParen], t))
        }
        Ok(HExpr::Antiquote(e.into()))
      }
      HLToken::Place => {
        Ok(HExpr::Place)
      }
      HLToken::QuoTy |
      HLToken::IotaTy |
      HLToken::BitTy |
      HLToken::OctTy |
      HLToken::IntTy |
      HLToken::FlpTy => {
        Ok(HExpr::Typat(HTypat::from(tok).into()))
      }
      HLToken::Iota => {
        Ok(HExpr::IotaLit)
      }
      HLToken::Tee => {
        Ok(HExpr::TeeLit)
      }
      HLToken::Bot => {
        Ok(HExpr::BotLit)
      }
      HLToken::Truth => {
        Ok(HExpr::BitLit(true))
      }
      HLToken::False => {
        Ok(HExpr::BitLit(false))
      }
      HLToken::IntLit(x) => {
        match self.current_token() {
          HLToken::Ident(name) => {
            // FIXME
            return Err(HError::Reserved("dimensional literals".to_owned()));
          }
          _ => {}
        }
        Ok(HExpr::IntLit(x))
      }
      HLToken::FlpLit(x) => {
        match self.current_token() {
          HLToken::Ident(name) => {
            // FIXME
            return Err(HError::Reserved("dimensional literals".to_owned()));
          }
          _ => {}
        }
        Ok(HExpr::FlpLit(x))
      }
      HLToken::Ident(name) => {
        Ok(HExpr::Ident(name))
      }
      /*HLToken::TyvarIdent(name) => {
        Ok(HExpr::Typat(HTypat::Tyvar(name).into()))
      }*/
      HLToken::StagingIdent(mut name) => {
        name.replace_range(.. 1, "");
        Ok(HExpr::StagingIdent(name))
      }
      HLToken::StagingIndex(mut name) => {
        name.replace_range(.. 1, "");
        Ok(HExpr::StagingIndex(name.parse().map_err(|_| HError::ExpectedIntLit)?))
      }
      HLToken::CrypticIdent(mut name) => {
        name.replace_range(.. 1, "");
        Ok(HExpr::CrypticIdent(name))
      }
      HLToken::UseIdent(mut name) => {
        name.replace_range(.. 1, "");
        Ok(HExpr::UseIdent(name))
      }
      _ => {
        Err(HError::Unknown)
      }
    }
  }

  fn led(&mut self, tok: HLToken, left: HExpr) -> Result<HExpr, HError> {
    // TODO
    match tok {
      HLToken::_Eof => {
        Err(HError::Eof)
      }
      HLToken::Dot => {
        match self.current_token() {
          // TODO: finalize the set of terms allowed on RHS.
          HLToken::IntLit(idx) => {
            self.advance();
            if idx < 1 {
              return Err(HError::Other);
            }
            Ok(HExpr::PathIndex(Rc::new(left), idx as _))
          }
          HLToken::Ident(name) => {
            self.advance();
            Ok(HExpr::PathLookup(Rc::new(left), name))
          }
          //_ => panic!(),
          _ => {
            let right = self.expression(self.lbp(&tok))?;
            Ok(HExpr::PathELookup(Rc::new(left), Rc::new(right)))
          }
        }
      }
      HLToken::As => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Alias(Rc::new(left), Rc::new(right)))
      }
      /*HLToken::RArrow => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Arrow(Rc::new(left), Rc::new(right)))
      }*/
      HLToken::PlusPlus => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Concat(Rc::new(left), Rc::new(right)))
      }
      /*HLToken::ColonColon => {
        let right = self.expression(self.lbp(&tok) - 1)?;
        Ok(HExpr::Cons(Rc::new(left), Rc::new(right)))
      }*/
      //HLToken::BarBar |
      HLToken::BackslashSlash => {
        let right = self.expression(self.lbp(&tok) - 1)?;
        Ok(HExpr::ShortOr(Rc::new(left), Rc::new(right)))
      }
      //HLToken::HatHat |
      HLToken::SlashBackslash => {
        let right = self.expression(self.lbp(&tok) - 1)?;
        Ok(HExpr::ShortAnd(Rc::new(left), Rc::new(right)))
      }
      HLToken::EqEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Eq(Rc::new(left), Rc::new(right)))
      }
      HLToken::NotEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::NotEq(Rc::new(left), Rc::new(right)))
      }
      HLToken::Gt => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Gt(Rc::new(left), Rc::new(right)))
      }
      HLToken::GtEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::GtEq(Rc::new(left), Rc::new(right)))
      }
      HLToken::Lt => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Lt(Rc::new(left), Rc::new(right)))
      }
      HLToken::LtEquals => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::LtEq(Rc::new(left), Rc::new(right)))
      }
      /*//HLToken::Bar => {
      HLToken::BarBar => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Or(Rc::new(left), Rc::new(right)))
      }
      HLToken::Hat => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::And(Rc::new(left), Rc::new(right)))
      }*/
      HLToken::Plus => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Add(Rc::new(left), Rc::new(right)))
      }
      HLToken::Dash => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Sub(Rc::new(left), Rc::new(right)))
      }
      HLToken::Star => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Mul(Rc::new(left), Rc::new(right)))
      }
      HLToken::Slash => {
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Div(Rc::new(left), Rc::new(right)))
      }
      HLToken::InfixIdent(ref infix_name) => {
        let mut name = infix_name.clone();
        name.replace_range(.. 1, "");
        let right = self.expression(self.lbp(&tok))?;
        Ok(HExpr::Infix(name, Rc::new(left), Rc::new(right)))
      }
      HLToken::PostfixIdent(ref postfix_name) => {
        let mut name = postfix_name.clone();
        name.replace_range(.. 1, "");
        Ok(HExpr::Postfix(name, Rc::new(left)))
      }
      HLToken::LBrack => {
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
            return Ok(HExpr::Apply(Rc::new(left), vec![]));
          }
          //HLToken::Comma => panic!(),
          HLToken::Comma => return Err(HError::Unexpected(HLToken::Comma)),
          _ => {}
        }
        let right = self.expression(0)?;
        match self.current_token() {
          HLToken::RBrack => {
            self.advance();
            return Ok(HExpr::Apply(Rc::new(left), vec![Rc::new(right)]));
          }
          HLToken::Comma => {
            let mut args = vec![Rc::new(right)];
            loop {
              self.advance();
              let right = self.expression(0)?;
              args.push(Rc::new(right));
              match self.current_token() {
                HLToken::RBrack => {
                  self.advance();
                  assert!(args.len() >= 2);
                  return Ok(HExpr::Apply(Rc::new(left), args));
                }
                HLToken::Comma => {}
                //_ => panic!(),
                t => return Err(HError::Expected(vec![HLToken::RBrack, HLToken::Comma], t))
              }
            }
          }
          //_ => panic!(),
          t => return Err(HError::Expected(vec![HLToken::RBrack, HLToken::Comma], t))
        }
      }
      _ => {
        Err(HError::Unknown)
      }
    }
  }

  fn expression(&mut self, rbp: i32) -> Result<HExpr, HError> {
    let (mut t, tinfo) = self.current_token_();
    self.advance();
    let mut left = self.nud(t, tinfo)?;
    t = self.current_token();
    while rbp < self.lbp(&t) {
      self.advance();
      left = self.led(t, left)?;
      t = self.current_token();
    }
    Ok(left)
  }

  pub fn parse(mut self) -> Result<Rc<HExpr>, HError> {
    self.advance();
    match self.expression(0) {
      Ok(expr) => Ok(Rc::new(expr)),
      Err(err) => match self.previous_token_info() {
        None => {
          println!("TRACE: parse error: {:?}", err);
          Err(err)
        }
        Some(info) => {
          println!("TRACE: parse error at {}:{}: {:?}", info.line_nr + 1, info.line_pos + 1, err);
          Err(err)
        }
      }
    }
  }
}
