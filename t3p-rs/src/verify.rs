use super::basic::*;
use std::rc::Rc;

type Bch = Vec<Rc<Form>>;

fn mk_vars_asc(k: u64) -> Vec<Term> {
  (0..k).map(|x| Term::Var(x)).collect()
}

fn mk_vars_desc(k: u64) -> Vec<Term> {
  (0..k).rev().map(|x| Term::Var(x)).collect()
}

fn is_vars(k: u64, ts: &Vec<Term>) -> bool {
  *ts == mk_vars_asc(k) || *ts == mk_vars_desc(k)
}

fn choice_axiom(k: u64, f: &Form) -> bool {
  match remove_fas(0,f) {
    (m, Form::Bct(Bct::Imp, f,g)) => {
      match &**f {
        Form::Qtf(true, h) => {
          form_below(k,h) && 
          (
            substform(0, &mk_par_term(k, mk_vars_asc(m)), h) == **g ||
            substform(0, &mk_par_term(k, mk_vars_desc(m)), h) == **g 
          )
        },
        _ => false
      }
    },
    _ => false
  }
}

fn pred_def(k: u64, f: &Form) -> bool {
  let (m,g) = remove_fas(0,f);
  match g {
    Form::Bct(Bct::Iff, h,p) => {
      match &**h {
        Form::Rel(j, ts) => {
          match &**j {
            FS::Par(n) => {
              k == *n && 
              form_below(k, p) && 
              is_vars(m, ts) 
            },
            _ => false
          }
        },
        _ => false
      }
    }
    _ => false
  }
}

fn remove_fas(c: u64, f: &Form) -> (u64, &Form) {
  match f { 
    Form::Qtf(false, g) => remove_fas(c+1,&*g),
    _ => (c, f)
  }
}

fn mono_args(k: u64) -> (Vec<Term>, Vec<Term>) {
  (
    (0..k).rev().map(|x| Term::Var((x*2)+1)).collect(), 
    (0..k).rev().map(|x| Term::Var(x*2)).collect()
  )
}
  
fn mono_body(k: u64, f: &Form) -> Option<(u64, &Form)> {
  match remove_fas(0, f) {
    (2, Form::Bct(Bct::Imp, g,h)) => {
      if is_eq(Term::Var(1), Term::Var(0), g) { mono_body(k+1, h) } 
      else { None }
    },
    (0, _) => Some((k,f)), 
    _ => None
  }
}

fn mono_fun(f: &Form) -> bool {
  match mono_body(0,f) {
    Some((k, Form::Rel(e,ts))) => {
      match &ts[..] {
        [Term::Fun(f0,ts0),Term::Fun(f1,ts1)] => {
          let (ss0,ss1) = mono_args(k);
          **e == FS::Atm("=".to_string()) && 
          *f0 == *f1 &&
          *ts0 == ss0 && *ts1 == ss1
        },
        _ => false
      }
    },
    _ => false
  }
}
    
fn mono_rel(f: &Form) -> bool {
  match mono_body(0,f) {
    Some((k, Form::Bct(Bct::Imp, g,h))) => {
      match (&**g,&**h) {
        (Form::Rel(ft0,ts0), Form::Rel(ft1,ts1)) => {
          let (ss0,ss1) = mono_args(k);
          *ft0 == *ft1 && *ts0 == ss0 && *ts1 == ss1
        },
        _ => false
      }
    },
    _ => false
  }
}

fn trans_axiom(f: &Form) -> bool {
  match remove_fas(0,f) {
    (3, Form::Bct(Bct::Imp, g,h)) => {
      is_eq(Term::Var(2), Term::Var(1), g) &&
      match &**h {
        Form::Bct(Bct::Imp, i,j) => 
          is_eq(Term::Var(1), Term::Var(0), i) &&
          is_eq(Term::Var(2), Term::Var(0), j),
        _ => false
      }
    },
    _ => false
  }
}

fn refl_axiom(f: &Form) -> bool {
  match f {
    Form::Qtf(false, g) => is_eq(Term::Var(0), Term::Var(0), g),
    _ => false 
  }
}

fn symm_axiom(f: &Form) -> bool { 
  match f { 
    Form::Qtf(false, g) => {
      match &**g {
        Form::Qtf(false, h) => {
          match &**h {
            Form::Bct(Bct::Imp, i,j) => {
              is_eq(Term::Var(1), Term::Var(0), &*i) &&
              is_eq(Term::Var(0), Term::Var(1), &*j) 
            },
            _ => false
          }
        },
        _ => false
      }
    },
    _ => false 
  }
}

fn is_not_false(f: &Form) -> bool {
  match &*f {
    Form::Not(g) => **g == Form::Cst(false),
    _ => false
  }
}

fn justified(k: u64, f: &Form) -> bool {
  (*f == Form::Cst(true)) ||
  is_not_false(f) ||
  refl_axiom(f) ||
  symm_axiom(f) ||
  trans_axiom(f) ||
  mono_rel(f) ||
  mono_fun(f) ||
  choice_axiom(k,f) ||
  pred_def(k,f) 
}

fn symb_below(k: u64, f: &FS) -> bool {
  match f {
    FS::Par(m) => *m < k,
    _ => true
  }
}

// fn not_rc(f: Form) -> Form { Form::Not(Rc::new(f)) }
fn rc_not(f: Rc<Form>) -> Rc<Form> { Rc::new(Form::Not(f)) }
fn rc_not_rc(f: Form) -> Rc<Form> { Rc::new(Form::Not(Rc::new(f))) }

fn term_below(k: u64, t: &Term) -> bool {
  match t {
    // Term::Dst(_) => true,
    // Term::Num(_) => true,
    Term::Var(_) => true,
    Term::Fun(f,ts) => 
      symb_below(k, &*f) && ts.iter().fold(true, |a, x| { a && term_below(k, x) })
  }
}

fn form_below(k: u64, f: &Form) -> bool {
  match f {
    Form::Cst(_) => true,
    Form::Not(g) => form_below(k,g),
    Form::Bct(_, g,h) => form_below(k,g) && form_below(k,h),
    Form::Qtf(_, g) => form_below(k,g),
    Form::Rel(_,ts) => ts.iter().fold(true, |a, x| { a && term_below(k,x) })
  }
}

fn mk_par_term(n: u64, ts: Vec<Term>) -> Term {
  Term::Fun(Rc::new(FS::Par(n)), ts)
}

fn ab(d: bool, f: Rc<Form>) -> Rc<Form> {
  match (d,&*f) {
    (false, Form::Not(g)) => {
      match &**g {
        Form::Bct(Bct::Or, h,_) => rc_not(h.clone()),
        Form::Bct(Bct::Imp,h,_) => h.clone(),
        _ => panic!("Not an A-formula")
      }
    },
    (true, Form::Not(g)) => {
      match &**g {
        Form::Bct(Bct::Or, _,h) => rc_not(h.clone()),
        Form::Bct(Bct::Imp,_,h) => rc_not(h.clone()),
        _ => panic!("Not an A-formula")
      }
    },
    (false, Form::Bct(Bct::And,g,_)) => g.clone(),
    (true,  Form::Bct(Bct::And,_,g)) => g.clone(),
    (false, Form::Bct(Bct::Iff,g,h)) => Rc::new(Form::Bct(Bct::Imp,g.clone(),h.clone())),
    (true,  Form::Bct(Bct::Iff,g,h)) => Rc::new(Form::Bct(Bct::Imp,h.clone(),g.clone())),
    _ => panic!("Not an A-formula")
  }
}

fn bb(f: Rc<Form>) -> (Rc<Form>, Rc<Form>) {
  match &*f {
    Form::Not(g) => {
      match &**g {
        Form::Bct(Bct::And,i,j) => (rc_not(i.clone()),rc_not(j.clone())), 
        Form::Bct(Bct::Iff,i,j) => (
          rc_not_rc(Form::Bct(Bct::Imp,i.clone(),j.clone())),
          rc_not_rc(Form::Bct(Bct::Imp,j.clone(),i.clone()))
        ),
        _ => panic!("Not a B-formula")
      }
    },
    Form::Bct(Bct::Or,f,g)  => (f.clone(), g.clone()),
    Form::Bct(Bct::Imp,f,g) => (rc_not(f.clone()), g.clone()),
    _ => panic!("Not a B-formula")
  }
}

fn cb(t: Term, f: Rc<Form>) -> Rc<Form> {
  match &*f {
    Form::Qtf(false,g) => Rc::new(substform(0,&t,&*g)),
    Form::Not(g) => {
      match &**g {
        Form::Qtf(true,h) => rc_not_rc(substform(0,&t,&*h)),
        _ => panic!("Not a C-formula : {:?}\nCannot instantiate with term : {:?}", f, t)
      }
    },
    _ => panic!("Not a C-formula : {:?}\nCannot instantiate with term : {:?}", f, t)
  }
}

fn db(n: u64, f: Rc<Form>) -> Rc<Form> {
  match &*f {
    Form::Qtf(true,g) => Rc::new(substform(0,&mk_par_term(n,vec![]),&*g)),
    Form::Not(g) => {
      match &**g {
        Form::Qtf(false,h) => rc_not_rc(substform(0,&mk_par_term(n,vec![]),&*h)),
        _ => panic!("Not a D-formula")
      }
    },
    _ => panic!("Not a D-formula")
  }
}

fn nb(f: Rc<Form>) -> Rc<Form> {
  match &*f {
    Form::Not(g) => {
      match &**g {
        Form::Not(h) => h.clone(),
        _ => panic!(format!("Not a N-formula : {:?}", *f))
      }
    },
    _ => panic!(format!("Not a N-formula : {:?}", *f))
  }
}

fn substterm(k: u64, t: &Term, s: &Term) -> Term {
  match s {
    Term::Var(m) => {
      if k < *m { Term::Var(m-1) } 
      else if k == *m { t.clone() } 
      else { Term::Var(*m) }
    },
    Term::Fun(f,ts) => Term::Fun(f.clone(),ts.iter().map(|x| substterm(k,t,x)).collect()),
    // Term::Dst(d) => Term::Dst(d.clone()),
    // Term::Num(s) => Term::Num(s.clone())
  }
}

fn incrvarterm(t: &Term) -> Term {
  match t {
    Term::Var(m) => Term::Var(m+1), 
    Term::Fun(f,ts) => Term::Fun(f.clone(),ts.iter().map(|x| incrvarterm(x)).collect()),
    // Term::Dst(d) => Term::Dst(d.clone()),
    // Term::Num(d) => Term::Num(d.clone())
  }
}

fn substform(n: u64, t: &Term, f: &Form) -> Form {
  match f {
    Form::Cst(b) => Form::Cst(*b),
    Form::Not(g) => Form::Not(Rc::new(substform(n,t,&*g))),
    Form::Bct(b,g,h)  => Form::Bct(*b,Rc::new(substform(n,t,&*g)),Rc::new(substform(n,t,&*h))),
    Form::Qtf(q,g) => Form::Qtf(*q,Rc::new(substform(n+1,&incrvarterm(t),&*g))),
    Form::Rel(s,ts) => Form::Rel(s.clone(),ts.iter().map(|x| substterm(n,t,x)).collect())
  }
}

fn get_from_context<'a>(ctx: &'a Bch, i: u64) -> Rst<Rc<Form>> {
  match ctx.get(i as usize) {
    Some(x) => Ok(x.clone()),
    _ => err_str("Cannot find premise in context")
  }
}

fn push_conc(ctx: &mut Bch, f: Rc<Form>) -> () {
  // println!("Branch length = {}", ctx.len());
  // println!("New premise = {}", *f);
  ctx.push(f);
}

fn check(mut ctx: Bch, bs: ReadBytesRef) -> Result<(), String> {
    
  let mut conts: Vec<(u64, Rc<Form>)> = vec![];

  loop {
    match get_char(bs)? {
      'A' => {
        let i = get_u64(bs)?; 
        let d = get_bool(bs)?;
        let p = get_from_context(&ctx, i)?;
        let c = ab(d,p);
        push_conc(&mut ctx,c);
      },
      'B' => {
        let i = get_u64(bs)?; 
        let p = get_from_context(&ctx, i)?;
        let (cl, cr) = bb(p);
        conts.push((ctx.len() as u64, cr)); 
        push_conc(&mut ctx,cl);
      },
      'C' => {
        let i = get_u64(bs)?; 
        let t = get_term(bs)?; 
        let p = get_from_context(&ctx, i)?;
        if !term_below((ctx.len()+1) as u64, &t) { return err_str("Instantiation term contains OOB parameter.") };
        let c = cb(t,p);
        push_conc(&mut ctx,c);
      },
      'D' => {
        let i = get_u64(bs)?; 
        let p = get_from_context(&ctx, i)?;
        let c = db(ctx.len() as u64,p);
        push_conc(&mut ctx,c);
      },
      'S' => {
        let f = get_form(bs)?;
        // if !ground_form(0, &f)  { return err_str("Cut formula is not ground.") };
        if !form_below((ctx.len()+1) as u64, &f) { return err_str("Cut formula contains OOB parameter.") };
        let x = Rc::new(f);
        conts.push((ctx.len() as u64, x.clone())); 
        push_conc(&mut ctx, rc_not(x));
      },
      'N' => {
        let i = get_u64(bs)?; 
        let p = get_from_context(&ctx, i)?;
        let c = nb(p);
        push_conc(&mut ctx, c);
      },
      'T' => {
        let f = get_form(bs)?;
        // if !ground_form(0,&f) { return err_str("Axiom is not ground.") };
        if !form_below((ctx.len()+1) as u64,&f) { return Err(format!("{:?} =< Parameter in axiom = {:?}", ctx.len(), f)) };
        if !justified(ctx.len() as u64, &f) { return err_str("Axiom unjustified.") };
        push_conc(&mut ctx, Rc::new(f));
      },
      'X' => { 
        let ni = get_u64(bs)?; 
        let pi = get_u64(bs)?; 
        let pf = get_from_context(&ctx, pi)?;
        match &*get_from_context(&ctx, ni)? {
          Form::Not(nf) => {
            if *pf == **nf { 
              match conts.pop() {
                Some((lth, sf)) => {
                  ctx.truncate(lth as usize);
                  ctx.push(sf);
                },
                None => return Ok(())
              }
            }
            else { 
              return Err(format!("Branch closure error. Positive = {:?} : {:?}. Negative = {:?} : Not({:?})", pi, pf, ni, nf)) 
            }
          }
          g => {
            return Err(format!("Branch closure error. Positive = {:?} : {:?}. Negative = {:?} : {:?}", pi, pf, ni, g)) 
          }
        }
      },
      c => return Err(format!("Invalid head character of subproof = {:?}", c))
    }
  }
}

fn process_inst(i: Inst) -> Rc<Form> {
  match i {
    (_,true,f,None) => {
      assert!(form_below(0, &f), "Bad formula in TPTP problem");
      Rc::new(f)
    }, 
    _ => panic!("Invalid inst")
  } 
}

 
// fn main() {
//   std::process::exit(
//     match body() {
//       Ok(()) => {
//         println!("Proof verified (kernel = RTTV).");
//         0
//       },
//       Err(msg) => {
//         println!("Invalid proof : {:?}", msg);
//         1
//       }
//     }
//   );
// }

pub fn main<I: Iterator<Item=String>>(mut args: I) -> Rst<()> {
  let tptp = args.next().expect("missing TPTP file");
  let tesc = args.next().expect("missing TESC file");

  let bch: Bch = conv_tptp_file(&tptp).into_iter().map(|x| process_inst(x)).collect();
  let mut prf: ReadBytes = get_read_bytes(&tesc, "Cannot open TESC file");

  check(bch, &mut prf)?;
  println!("Proof verified by OTV.");
  Ok(())
}
