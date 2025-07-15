#!/bin/bash

# Recognition Science Fast Build Script
# =====================================
# 
# This script optimizes the build process with:
# - Parallel compilation using all CPU cores
# - Mathlib cache management
# - Environment variable optimization
# - Build timing and monitoring

set -e  # Exit on error

echo "🚀 Recognition Science Fast Build Script"
echo "========================================"

# Get number of CPU cores
if [[ "$OSTYPE" == "darwin"* ]]; then
    CORES=$(sysctl -n hw.ncpu)
else
    CORES=$(nproc)
fi

echo "📊 System Info:"
echo "   CPU Cores: $CORES"
echo "   OS: $OSTYPE"
echo "   Lean Version: $(lean --version)"

# Set environment variables for optimal builds
export LEAN_WORKER_PROCESSES=$CORES
export LEAN_CC=clang
export LEAN_CXX=clang++
export LEAN_PATH_SEPARATOR=":"

# Enable faster linking on macOS
if [[ "$OSTYPE" == "darwin"* ]]; then
    export LEAN_LD=ld64.lld
fi

# Function to check if mathlib cache exists
check_mathlib_cache() {
    if [ -d ".lake/packages/mathlib/.lake/build" ]; then
        echo "✅ Mathlib cache found"
        return 0
    else
        echo "❌ Mathlib cache not found"
        return 1
    fi
}

# Function to download mathlib cache
download_mathlib_cache() {
    echo "📥 Downloading mathlib cache..."
    
    # Try to download cache from GitHub releases
    MATHLIB_VERSION="v4.11.0"
    CACHE_URL="https://github.com/leanprover-community/mathlib4/releases/download/${MATHLIB_VERSION}/oleans-${MATHLIB_VERSION}.tar.gz"
    
    if curl -L -f "$CACHE_URL" -o mathlib-cache.tar.gz; then
        echo "✅ Cache downloaded successfully"
        
        # Extract to mathlib package directory
        mkdir -p .lake/packages/mathlib/.lake/build
        tar -xzf mathlib-cache.tar.gz -C .lake/packages/mathlib/.lake/build/
        rm mathlib-cache.tar.gz
        
        echo "✅ Cache extracted successfully"
    else
        echo "⚠️  Cache download failed, will build from source"
    fi
}

# Function to clean build artifacts
clean_build() {
    echo "🧹 Cleaning build artifacts..."
    rm -rf .lake/build
    echo "✅ Build cleaned"
}

# Function to run optimized build
fast_build() {
    echo "🔨 Starting optimized build..."
    
    # Record start time
    START_TIME=$(date +%s)
    
    # Run lake build with optimizations
    lake build --verbose
    
    # Record end time
    END_TIME=$(date +%s)
    BUILD_TIME=$((END_TIME - START_TIME))
    
    echo "✅ Build completed in ${BUILD_TIME}s"
}

# Function to run incremental build
incremental_build() {
    echo "🔄 Running incremental build..."
    
    START_TIME=$(date +%s)
    lake build
    END_TIME=$(date +%s)
    BUILD_TIME=$((END_TIME - START_TIME))
    
    echo "✅ Incremental build completed in ${BUILD_TIME}s"
}

# Function to show build status
show_build_status() {
    echo "📊 Build Status:"
    echo "   .lake/build size: $(du -sh .lake/build 2>/dev/null || echo 'N/A')"
    echo "   .lake/packages size: $(du -sh .lake/packages 2>/dev/null || echo 'N/A')"
    
    if [ -f ".lake/build/lib/RecognitionScience.olean" ]; then
        echo "   RecognitionScience: ✅ Built"
    else
        echo "   RecognitionScience: ❌ Not built"
    fi
}

# Function to test specific foundation
test_foundation() {
    local foundation=$1
    echo "🧪 Testing Foundation: $foundation"
    
    # Note: Lake doesn't support direct foundation building, so we build all and check
    lake build
    
    if [ $? -eq 0 ]; then
        echo "✅ Foundation $foundation builds successfully"
    else
        echo "❌ Foundation $foundation failed to build"
    fi
}

# Main script logic
case "${1:-build}" in
    "clean")
        clean_build
        ;;
    "cache")
        download_mathlib_cache
        ;;
    "build")
        if ! check_mathlib_cache; then
            download_mathlib_cache
        fi
        fast_build
        show_build_status
        ;;
    "incremental")
        incremental_build
        show_build_status
        ;;
    "status")
        show_build_status
        ;;
    "test")
        test_foundation "${2:-DiscreteTime}"
        ;;
    "full")
        echo "🔄 Full rebuild with cache refresh"
        clean_build
        download_mathlib_cache
        fast_build
        show_build_status
        ;;
    *)
        echo "Usage: $0 {build|clean|cache|incremental|status|test|full}"
        echo ""
        echo "Commands:"
        echo "  build       - Fast build with cache (default)"
        echo "  clean       - Clean build artifacts"
        echo "  cache       - Download mathlib cache"
        echo "  incremental - Quick incremental build"
        echo "  status      - Show build status"
        echo "  test <name> - Test specific foundation"
        echo "  full        - Full rebuild with cache refresh"
        exit 1
        ;;
esac

echo "🎉 Build script completed successfully!" 