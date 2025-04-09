use std::io::{Read, Write};
use std::process::{Command, Stdio};
use std::env;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env::set_current_dir("___full__path___")?;
    // let path = env::current_dir()?;
    // println!("The current directory is {}", path.display());

    let cmd = "___full__path___/.lake/build/bin/runner";

    // let output = Command::new("lake")
    // .arg("env")
    // .output()
    // .expect("Failed to execute command");

    // println!("stdout: {}", String::from_utf8_lossy(&output.stdout));


    let mut child = Command::new("lake")
        .args(["env", cmd])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Error");

    let mut stdin = child.stdin.take().expect("Stdin error");
    let mut stdout = child.stdout.take().expect("Failed to open stdout");

    stdin
        .write_all("import Mathlib.Topology.Basic\n#check TopologicalSpace".as_bytes())
        .expect("Writeall error");

    drop(stdin);
    let mut output = String::new();

    stdout.read_to_string(&mut output).expect("msg");

    println!("{}", output);

    child.wait().expect("Failed to wait on child");

    Ok(())
}
