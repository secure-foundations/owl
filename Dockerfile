FROM ubuntu:22.04

# Avoid interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Set locale
ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8

# Install system dependencies
RUN apt-get update && apt-get install -y \
    curl \
    wget \
    git \
    build-essential \
    pkg-config \
    libssl-dev \
    libgmp-dev \
    libtinfo-dev \
    zlib1g-dev \
    libncurses5-dev \
    libncursesw5-dev \
    libtinfo5 \
    python3 \
    python3-pip \
    unzip \
    ca-certificates \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

# Install Python packages
RUN pip3 install prettytable matplotlib numpy

# Set environment variables for root user
ENV PATH="/root/.ghcup/bin:/root/.cargo/bin:${PATH}"
ENV GHCUP_INSTALL_BASE_PREFIX="/root"
WORKDIR /root

# Install GHCup and GHC 9.0.2 with non-interactive mode
RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | \
    BOOTSTRAP_HASKELL_NONINTERACTIVE=1 \
    BOOTSTRAP_HASKELL_NO_UPGRADE=1 \
    BOOTSTRAP_HASKELL_MINIMAL=1 \
    sh && \
    . /root/.ghcup/env && \
    ghcup install ghc 9.0.2 && \
    ghcup set ghc 9.0.2

# Install Cabal 3.6.2.0
RUN . /root/.ghcup/env && \
    ghcup install cabal 3.6.2.0 && \
    ghcup set cabal 3.6.2.0

# Install Rustup and Rust 1.82
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain 1.82.0 && \
    . /root/.cargo/env

# Install verusfmt via cargo
RUN . /root/.cargo/env && \
    cargo install verusfmt --version 0.4.3

# Install Tokei for line counting
RUN . /root/.cargo/env && \
    cargo install tokei

# Download and install Verus release 0.2025.04.12.04a69f9 (also installs z3)
RUN wget https://github.com/verus-lang/verus/releases/download/release%2F0.2025.04.12.04a69f9/verus-0.2025.04.12.04a69f9-x86-linux.zip && \
    unzip verus-0.2025.04.12.04a69f9-x86-linux.zip -d /root/verus && \
    rm verus-0.2025.04.12.04a69f9-x86-linux.zip


# Add Verus to PATH (also adds z3 to PATH)
ENV PATH="/root/verus/verus-x86-linux:${PATH}"

# Verify installations
RUN . /root/.ghcup/env && \
    . /root/.cargo/env && \
    echo "=== Check versions: ===" && \
    ghc --version && \
    cabal --version && \
    rustc --version && \
    z3 --version && \
    cargo --version && \
    verusfmt --version && \
    verus --version 

# Set up environment for interactive use
RUN echo 'source /root/.ghcup/env' >> /root/.bashrc && \
    echo 'source /root/.cargo/env' >> /root/.bashrc

# Create the owlc directory
RUN mkdir -p /root/owlc

# Copy the current directory contents to /root/owlc/ for building
COPY . /root/owlc/

# Build owlc
WORKDIR /root/owlc
RUN . /root/.ghcup/env && \
    cabal update && \
    cabal build owl

CMD ["/bin/bash"]