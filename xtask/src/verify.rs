use std::{
    env, fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{SystemTime, UNIX_EPOCH},
};

use anyhow::{bail, Context};
use clap::Parser;
use json::JsonValue;

use crate::kernel::{self, BuildOptions};

const DEFAULT_VERUS_RELEASE: &str = "release/0.2026.04.12.f1166c4";
const DEFAULT_VERIFY_TOOLCHAIN: &str = "1.94.0-x86_64-unknown-linux-gnu";
const DEFAULT_VERIFY_MAX_ERRORS: usize = 1;
const DEFAULT_VERIFY_JOBS: usize = 1;
const VERUS_ASSET_SUFFIX: &str = "x86-linux.zip";

#[derive(Debug, Parser, Clone)]
pub struct BootstrapOptions {
    #[clap(long, help = "Install directory for Verus release binaries")]
    pub install_dir: Option<PathBuf>,
    #[clap(long, help = "Verus release tag, or 'latest'")]
    pub verus_release: Option<String>,
    #[clap(
        long,
        default_value_t = false,
        help = "Redownload even if cargo-verus already exists"
    )]
    pub force: bool,
}

#[derive(Debug, Parser, Clone)]
pub struct VerifyOptions {
    #[clap(
        default_value = "spike",
        short,
        long,
        help = "support spike and qemu-arm-virt"
    )]
    pub platform: String,
    #[clap(
        short,
        long,
        default_value_t = false,
        help = "Enable MCS support if set to true or on"
    )]
    pub mcs: bool,
    #[clap(
        short,
        long,
        default_value_t = false,
        help = "Enable SMC support if set to true or on"
    )]
    pub smc: bool,
    #[clap(long, help = "Disable fastpath feature")]
    pub nofastpath: bool,
    #[clap(
        long,
        default_value_t = false,
        help = "Enable pcnt regs read/write in userspace"
    )]
    pub arm_pcnt: bool,
    #[clap(
        long,
        default_value_t = false,
        help = "Enable ptmr regs read/write in userspace"
    )]
    pub arm_ptmr: bool,
    #[clap(
        long,
        default_value_t = false,
        help = "Enable hypervisor feature(TODO)"
    )]
    pub arm_hypervisor: bool,
    #[clap(
        long,
        short = 'N',
        help = "Number of nodes in the system, if > 1, enable smp",
        default_value_t = 1
    )]
    pub num_nodes: usize,
    #[clap(long, default_value = "sel4_cspace", help = "Package to verify")]
    pub package: String,
    #[clap(
        long,
        default_value = "verify",
        help = "Feature list forwarded to cargo-verus"
    )]
    pub features: String,
    #[clap(long, help = "Rust toolchain used by cargo-verus")]
    pub toolchain: Option<String>,
    #[clap(long, help = "Parallel jobs forwarded to cargo-verus")]
    pub jobs: Option<usize>,
    #[clap(long, help = "Maximum number of verification errors to report")]
    pub max_errors: Option<usize>,
    #[clap(long, help = "Directory containing the Verus release binaries")]
    pub verus_release_dir: Option<PathBuf>,
    #[clap(long, help = "Path to the cargo-verus executable")]
    pub cargo_verus: Option<PathBuf>,
    #[clap(last = true, help = "Extra arguments forwarded to cargo-verus")]
    pub extra_args: Vec<String>,
}

pub fn bootstrap(opts: &BootstrapOptions) -> Result<(), anyhow::Error> {
    let project_root = project_root()?;
    let install_dir = opts
        .install_dir
        .as_deref()
        .map(|path| resolve_from_project_root(&project_root, path))
        .unwrap_or_else(|| project_root.join("tools/verus/release"));
    let verus_release = opts
        .verus_release
        .as_deref()
        .unwrap_or(DEFAULT_VERUS_RELEASE);
    let cargo_verus = install_dir.join("cargo-verus");

    for command in ["curl", "unzip", "find", "cp", "chmod", "rm"] {
        ensure_command_available(command)?;
    }

    if is_executable(&cargo_verus) && !opts.force {
        println!(
            "[bootstrap] cargo-verus already available at {} (set --force to redownload)",
            cargo_verus.display()
        );
        return Ok(());
    }

    let api_url = if verus_release == "latest" {
        "https://api.github.com/repos/verus-lang/verus/releases/latest".to_string()
    } else {
        format!("https://api.github.com/repos/verus-lang/verus/releases/tags/{verus_release}")
    };

    let release_json = curl_to_string(&api_url)?;
    let release_doc =
        json::parse(&release_json).context("failed to parse GitHub release metadata")?;
    let release_label = release_doc["tag_name"]
        .as_str()
        .unwrap_or(verus_release)
        .to_string();
    let asset_url = find_asset_url(&release_doc, VERUS_ASSET_SUFFIX)
        .context("failed to resolve Verus asset URL")?;

    let temp_dir = TempDirGuard::new("xtask-verus-bootstrap")?;
    let asset_file = temp_dir.path().join("verus-x86-linux.zip");

    println!("[bootstrap] downloading Verus binary ({release_label}, platform=x86-linux)");
    println!("[bootstrap] asset: {asset_url}");
    run_command(
        Command::new("curl")
            .arg("-fL")
            .arg(&asset_url)
            .arg("-o")
            .arg(&asset_file),
        "curl download",
    )?;

    println!("[bootstrap] extracting {}", asset_file.display());
    run_command(
        Command::new("unzip")
            .arg("-q")
            .arg(&asset_file)
            .arg("-d")
            .arg(temp_dir.path()),
        "unzip",
    )?;

    let cargo_verus_src = capture_stdout(
        Command::new("find")
            .arg(temp_dir.path())
            .arg("-type")
            .arg("f")
            .arg("-name")
            .arg("cargo-verus"),
        "find cargo-verus",
    )?
    .lines()
    .find(|line| !line.trim().is_empty())
    .map(PathBuf::from)
    .context("cargo-verus not found in extracted archive")?;
    let asset_root = cargo_verus_src
        .parent()
        .context("failed to resolve extracted Verus root directory")?;

    println!(
        "[bootstrap] installing Verus tools to {}",
        install_dir.display()
    );
    run_command(
        Command::new("rm").arg("-rf").arg(&install_dir),
        "rm -rf verus install dir",
    )?;
    fs::create_dir_all(&install_dir)
        .with_context(|| format!("failed to create {}", install_dir.display()))?;
    run_command(
        Command::new("cp")
            .arg("-a")
            .arg(format!("{}/.", asset_root.display()))
            .arg(&install_dir),
        "cp -a verus release",
    )?;
    run_command(
        Command::new("chmod")
            .arg("+x")
            .arg(install_dir.join("cargo-verus"))
            .arg(install_dir.join("rust_verify"))
            .arg(install_dir.join("verus")),
        "chmod +x verus tools",
    )?;

    if !is_executable(&cargo_verus) {
        bail!(
            "cargo-verus not found after install: {}",
            cargo_verus.display()
        );
    }

    println!("[bootstrap] bootstrap complete: {}", cargo_verus.display());
    Ok(())
}

pub fn run(opts: &VerifyOptions) -> Result<(), anyhow::Error> {
    let project_root = project_root()?;
    let build_opts = opts.build_options();
    let target = kernel::target_triple(&build_opts.platform)?;
    let marcos = kernel::build_marcos(&build_opts)?;
    let jobs = opts.jobs.unwrap_or_else(default_verify_jobs);
    let max_errors = opts.max_errors.unwrap_or(DEFAULT_VERIFY_MAX_ERRORS);
    let toolchain = opts
        .toolchain
        .as_deref()
        .unwrap_or(DEFAULT_VERIFY_TOOLCHAIN);
    let verus_release_dir = opts
        .verus_release_dir
        .as_deref()
        .map(|path| resolve_from_project_root(&project_root, path))
        .unwrap_or_else(|| project_root.join("tools/verus/release"));
    let cargo_verus = opts
        .cargo_verus
        .as_deref()
        .map(|path| resolve_from_project_root(&project_root, path))
        .unwrap_or_else(|| verus_release_dir.join("cargo-verus"));

    if !is_executable(&cargo_verus) {
        bail!(
            "[verify-official][error] missing cargo-verus at {}\n[verify-official][hint] expected release tools under {}\n[verify-official][hint] run: cargo xtask bootstrap-verus",
            cargo_verus.display(),
            verus_release_dir.display()
        );
    }

    println!("[verify-official] cargo-verus: {}", cargo_verus.display());
    println!(
        "[verify-official] package={} features={} target={target} jobs={jobs}",
        opts.package, opts.features
    );
    println!(
        "[verify-official] if output is delayed, Cargo may be waiting on lock /usr/local/cargo/.package-cache"
    );

    let mut command = Command::new(&cargo_verus);
    command
        .arg("verify")
        .arg("-p")
        .arg(&opts.package)
        .arg("--features")
        .arg(&opts.features)
        .arg("--")
        .arg(format!("--multiple-errors={max_errors}"))
        .current_dir(&project_root)
        .env("RUSTUP_TOOLCHAIN", toolchain)
        .env("RUSTC_BOOTSTRAP", "1")
        .env("PLATFORM", &opts.platform)
        .env("MARCOS", marcos.join(" "))
        .env("CARGO_BUILD_TARGET", target)
        .env("CARGO_BUILD_JOBS", jobs.to_string());

    if !opts.extra_args.is_empty() {
        command.args(&opts.extra_args);
    }

    println!(
        "Running Verus verify for package={} features={} platform={} target={}",
        opts.package, opts.features, opts.platform, target
    );
    run_command(&mut command, "cargo-verus verify")
}

impl VerifyOptions {
    fn build_options(&self) -> BuildOptions {
        BuildOptions {
            platform: self.platform.clone(),
            mcs: self.mcs,
            smc: self.smc,
            nofastpath: self.nofastpath,
            arm_pcnt: self.arm_pcnt,
            arm_ptmr: self.arm_ptmr,
            arm_hypervisor: self.arm_hypervisor,
            rust_only: false,
            bin: false,
            num_nodes: self.num_nodes,
            log: "INFO".to_string(),
            benchmark: false,
        }
    }
}

fn project_root() -> Result<PathBuf, anyhow::Error> {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .canonicalize()
        .context("failed to resolve xtask project root")
}

fn resolve_from_project_root(project_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        project_root.join(path)
    }
}

fn capture_stdout(command: &mut Command, step_name: &str) -> Result<String, anyhow::Error> {
    let output = command
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .output()
        .with_context(|| format!("failed to execute {step_name}"))?;

    if !output.status.success() {
        bail!("{step_name} exited with status {}", output.status);
    }

    String::from_utf8(output.stdout).context("command returned non-UTF-8 output")
}

fn curl_to_string(url: &str) -> Result<String, anyhow::Error> {
    capture_stdout(
        Command::new("curl").arg("-fsSL").arg(url),
        &format!("curl {url}"),
    )
}

fn find_asset_url(release_doc: &JsonValue, suffix: &str) -> Option<String> {
    release_doc["assets"].members().find_map(|asset| {
        let url = asset["browser_download_url"].as_str()?;
        url.ends_with(suffix).then(|| url.to_string())
    })
}

fn default_verify_jobs() -> usize {
    env::var("CARGO_BUILD_JOBS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|parallelism| {
                    let cpus = parallelism.get();
                    cpus.div_ceil(2).clamp(DEFAULT_VERIFY_JOBS, 4)
                })
                .unwrap_or(DEFAULT_VERIFY_JOBS)
        })
}

fn ensure_command_available(command: &str) -> Result<(), anyhow::Error> {
    if command_in_path(command) {
        Ok(())
    } else {
        bail!("missing required command: {command}")
    }
}

fn command_in_path(command: &str) -> bool {
    env::var_os("PATH")
        .into_iter()
        .flat_map(|paths| env::split_paths(&paths).collect::<Vec<_>>())
        .map(|dir| dir.join(command))
        .any(|path| is_executable(&path))
}

fn is_executable(path: &Path) -> bool {
    fs::metadata(path)
        .map(|metadata| metadata.is_file() && metadata.permissions().mode() & 0o111 != 0)
        .unwrap_or(false)
}

fn run_command(command: &mut Command, step_name: &str) -> Result<(), anyhow::Error> {
    let status = command
        .status()
        .with_context(|| format!("failed to execute {step_name}"))?;
    anyhow::ensure!(status.success(), "{step_name} exited with status {status}");
    Ok(())
}

struct TempDirGuard {
    path: PathBuf,
}

impl TempDirGuard {
    fn new(prefix: &str) -> Result<Self, anyhow::Error> {
        let mut base = env::temp_dir();
        let unique = format!(
            "{prefix}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .context("system clock is before UNIX_EPOCH")?
                .as_nanos()
        );
        base.push(unique);
        fs::create_dir_all(&base)
            .with_context(|| format!("failed to create temp dir {}", base.display()))?;
        Ok(Self { path: base })
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDirGuard {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}
