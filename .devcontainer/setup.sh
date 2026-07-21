#!/bin/zsh
set -e

# Copy shell configuration
cp .devcontainer/config/.zshrc ~/.zshrc
source ~/.zshrc
mkdir -p ~/.config
cp .devcontainer/config/starship.toml ~/.config/starship.toml

# Install elan (the Lean version manager) non-interactively.
# --no-modify-path: we put elan on PATH ourselves (below) instead of letting
# the installer edit shell profiles, keeping the copied ~/.zshrc predictable.
# Elan reads ./lean-toolchain and fetches the pinned Lean on demand; we
# pre-install it here so the editor is ready immediately on first open.
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --no-modify-path --default-toolchain none
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.zshrc
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$(cat lean-toolchain)"

# Install Claude Code CLI (native installer, auto-updates)
curl -fsSL https://claude.ai/install.sh | bash

# Configure Claude Code to skip permission prompts inside the container
mkdir -p ~/.claude
cat > ~/.claude/settings.json <<'EOF'
{
  "permissions": {
    "defaultMode": "bypassPermissions"
  },
  "env": {
    "ENABLE_CLAUDEAI_MCP_SERVERS": "false"
  }
}
EOF
