# Recognition Science Build Makefile
# =================================
#
# Fast build targets with parallel compilation and caching
#
# Usage:
#   make build      - Fast build with cache
#   make clean      - Clean build artifacts
#   make cache      - Download mathlib cache
#   make full       - Full rebuild with cache
#   make test       - Test all foundations
#   make status     - Show build status

.PHONY: build clean cache full test status incremental help

# Default target
all: build

# Fast build with cache
build:
	@echo "🚀 Starting fast build..."
	@./build.sh build

# Clean build artifacts
clean:
	@echo "🧹 Cleaning build artifacts..."
	@./build.sh clean

# Download mathlib cache
cache:
	@echo "📥 Downloading mathlib cache..."
	@./build.sh cache

# Full rebuild with cache refresh
full:
	@echo "🔄 Full rebuild with cache refresh..."
	@./build.sh full

# Incremental build (fastest)
incremental:
	@echo "⚡ Incremental build..."
	@./build.sh incremental

# Test all foundations
test:
	@echo "🧪 Testing all foundations..."
	@./build.sh test DiscreteTime
	@./build.sh test DualBalance
	@./build.sh test PositiveCost
	@./build.sh test UnitaryEvolution
	@./build.sh test IrreducibleTick
	@./build.sh test SpatialVoxels
	@./build.sh test EightBeat
	@./build.sh test GoldenRatio

# Show build status
status:
	@echo "📊 Build status..."
	@./build.sh status

# Direct lake commands with optimizations
lake-build:
	@echo "🔨 Direct lake build with optimizations..."
	@export LEAN_WORKER_PROCESSES=10 && lake build

lake-clean:
	@echo "🧹 Lake clean..."
	@lake clean

# Build specific foundation (builds all since Lake doesn't support individual targets)
foundation-%:
	@echo "🏗️  Building foundation: $*"
	@export LEAN_WORKER_PROCESSES=10 && lake build

# Development shortcuts
dev: incremental
	@echo "✅ Development build complete"

release: full
	@echo "🎉 Release build complete"

# Help target
help:
	@echo "Recognition Science Build System"
	@echo "==============================="
	@echo ""
	@echo "Available targets:"
	@echo "  build       - Fast build with cache (default)"
	@echo "  clean       - Clean build artifacts"
	@echo "  cache       - Download mathlib cache"
	@echo "  full        - Full rebuild with cache refresh"
	@echo "  incremental - Quick incremental build"
	@echo "  test        - Test all foundations"
	@echo "  status      - Show build status"
	@echo "  dev         - Development build (incremental)"
	@echo "  release     - Release build (full)"
	@echo ""
	@echo "Foundation-specific builds:"
	@echo "  foundation-DiscreteTime    - Build Foundation 1"
	@echo "  foundation-DualBalance     - Build Foundation 2"
	@echo "  foundation-PositiveCost    - Build Foundation 3"
	@echo "  foundation-UnitaryEvolution - Build Foundation 4"
	@echo "  foundation-IrreducibleTick - Build Foundation 5"
	@echo "  foundation-SpatialVoxels   - Build Foundation 6"
	@echo "  foundation-EightBeat       - Build Foundation 7"
	@echo "  foundation-GoldenRatio     - Build Foundation 8"
	@echo ""
	@echo "Direct lake commands:"
	@echo "  lake-build  - Direct optimized lake build"
	@echo "  lake-clean  - Direct lake clean" 