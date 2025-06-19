FROM ubuntu:22.04

# Avoid interactive prompts
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
    wireguard \
    iproute2 \
    iperf3 \
    iputils-ping \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

# Install Python packages
RUN pip3 install prettytable matplotlib numpy

ENV PATH="/root/.ghcup/bin:/root/.cargo/bin:/usr/local/go/bin:${PATH}"
ENV GHCUP_INSTALL_BASE_PREFIX="/root"
WORKDIR /root

# Install Go 1.20
RUN wget https://go.dev/dl/go1.20.linux-amd64.tar.gz && \
    tar -C /usr/local -xzf go1.20.linux-amd64.tar.gz && \
    rm go1.20.linux-amd64.tar.gz

# Install GHCup and GHC 9.0.2
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

# Install verusfmt
RUN . /root/.cargo/env && \
    cargo install verusfmt --version 0.4.3

# Install Tokei
RUN . /root/.cargo/env && \
    cargo install tokei

# Download and install Verus release 0.2025.04.12.04a69f9 and z3
RUN wget https://github.com/verus-lang/verus/releases/download/release%2F0.2025.04.12.04a69f9/verus-0.2025.04.12.04a69f9-x86-linux.zip && \
    unzip verus-0.2025.04.12.04a69f9-x86-linux.zip -d /root/verus && \
    rm verus-0.2025.04.12.04a69f9-x86-linux.zip


# Add Verus and z3 to PATH
ENV PATH="/root/verus/verus-x86-linux:${PATH}"

# Fetch wireguard-go
RUN git clone --depth 1 --no-tags https://github.com/WireGuard/wireguard-go.git /root/wireguard-go && \
    cd /root/wireguard-go && \
    git fetch --depth 1 origin 12269c2761734b15625017d8565745096325392f && \
    git checkout 12269c2761734b15625017d8565745096325392f

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
    verus --version && \
    go version

# Set up environment
RUN echo 'source /root/.ghcup/env' >> /root/.bashrc && \
    echo 'source /root/.cargo/env' >> /root/.bashrc

# Create the owlc directory
RUN mkdir -p /root/owlc

# Copy the current directory contents to /root/owlc/ for building
COPY . /root/owlc/

# Build OwlC
WORKDIR /root/owlc
RUN . /root/.ghcup/env && \
    cabal update && \
    cabal build owl

# Backup the cabal build artifacts
RUN cp -r /root/owlc/dist-newstyle /root/owlc-build-cached

# Create a script to restore build artifacts when source is mounted.
# Otherwise, we would have to rebuild OwlC when the container starts (takes ~20min).
# The script checks if there are saved build artifacts in `/root/owlc-build-cached`
# and no build artifacts in the working directory, and if so, restores the cached artifacts.
RUN echo '#!/bin/bash\n\
if [ ! -d "/root/owlc/dist-newstyle" ] && [ -d "/root/owlc-build-cached" ]; then\n\
    echo "Restoring build artifacts..."\n\
    cp -r /root/owlc-build-cached /root/owlc/dist-newstyle\n\
fi\n\
exec "$@"' > /root/entrypoint.sh && chmod +x /root/entrypoint.sh

ENTRYPOINT ["/root/entrypoint.sh"]
CMD ["/bin/bash"]