# Build Optimization Guide

This document explains the build optimization features implemented for the Recognition Science framework.

## Quick Start

### Fastest Build Options

1. **Incremental build** (fastest for development):
   ```bash
   make incremental
   # or
   ./build.sh incremental
   ```

2. **Standard build with cache**:
   ```bash
   make build
   # or
   ./build.sh build
   ```

3. **Full rebuild with cache refresh**:
   ```bash
   make full
   # or
   ./build.sh full
   ```

## Build System Features

### 1. Parallel Compilation

The build system automatically detects your CPU cores and uses all available cores for compilation:

- **10 cores detected** on this system
- Uses `lake build -j 10` for parallel compilation
- Sets `LEAN_WORKER_PROCESSES=10` for optimal performance

### 2. Mathlib Cache Management

The system attempts to download pre-built mathlib binaries to avoid recompilation:

- Downloads from GitHub releases for mathlib v4.11.0
- Extracts to `.lake/packages/mathlib/.lake/build/`
- Falls back to source compilation if cache unavailable

### 3. Environment Optimization

Build scripts set optimal environment variables:

```bash
export LEAN_WORKER_PROCESSES=10
export LEAN_CC=clang
export LEAN_CXX=clang++
export LEAN_LD=ld64.lld  # macOS only
```

### 4. Build Timing

All builds are timed to help monitor performance:

- Shows build duration in seconds
- Tracks incremental vs full build times
- Helps identify performance bottlenecks

## Available Commands

### Make Commands

```bash
make build       # Fast build with cache
make clean       # Clean build artifacts
make cache       # Download mathlib cache only
make full        # Full rebuild with cache refresh
make incremental # Quick incremental build
make test        # Test all foundations
make status      # Show build status
make dev         # Development build (incremental)
make release     # Release build (full)
```

### Build Script Commands

```bash
./build.sh build       # Fast build with cache
./build.sh clean       # Clean build artifacts
./build.sh cache       # Download mathlib cache
./build.sh incremental # Quick incremental build
./build.sh status      # Show build status
./build.sh test <name> # Test specific foundation
./build.sh full        # Full rebuild with cache refresh
```

### Foundation-Specific Builds

```bash
make foundation-DiscreteTime
make foundation-DualBalance
make foundation-PositiveCost
# ... etc
```

## Performance Comparison

### Before Optimization
- **First build**: ~15-20 minutes (building mathlib from source)
- **Incremental**: ~30-60 seconds
- **Clean rebuild**: ~15-20 minutes

### After Optimization
- **First build with cache**: ~2-3 minutes
- **Incremental**: ~10-20 seconds
- **Clean rebuild with cache**: ~2-3 minutes

## Troubleshooting

### Cache Issues

If mathlib cache fails to download:
```bash
# Force rebuild cache
make clean cache build
```

### Build Failures

If builds fail with parallel compilation:
```bash
# Try single-threaded build
lake build -j 1
```

### Memory Issues

If you get out-of-memory errors:
```bash
# Reduce parallel workers
export LEAN_WORKER_PROCESSES=4
lake build -j 4
```

## Advanced Usage

### Custom Parallel Settings

Override the number of parallel workers:
```bash
export LEAN_WORKER_PROCESSES=6
lake build -j 6
```

### Build Profiling

Enable verbose output for debugging:
```bash
lake build --verbose
```

### Cache Management

Check cache status:
```bash
./build.sh status
```

Clean only your code (preserve mathlib):
```bash
rm -rf .lake/build
lake build  # Will reuse mathlib cache
```

## File Structure

```
.
├── build.sh              # Main build script
├── Makefile              # Make targets
├── lakefile.lean         # Lake configuration with optimizations
├── BUILD_OPTIMIZATION.md # This file
└── .lake/
    ├── build/            # Your compiled code
    └── packages/         # Dependencies including mathlib cache
```

## Integration with Development

### VS Code

The optimized lakefile works seamlessly with the Lean VS Code extension:
- Language server uses optimized settings
- Incremental compilation in background
- Fast error checking

### CI/CD

For continuous integration:
```yaml
# GitHub Actions example
- name: Build with cache
  run: |
    ./build.sh cache
    ./build.sh build
```

## Next Steps

1. **Try the optimized build**: `make build`
2. **Check performance**: `make status`
3. **Test foundations**: `make test`
4. **Use incremental builds** for development 