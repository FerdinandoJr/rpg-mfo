# TLA+ Setup Guide

This guide provides three options for setting up TLA+ on your system. Follow the steps for the option that best suits your needs.

## Option 1: VS Code

### 1. Tutorial
- https://www.youtube.com/watch?v=sLGY7_agg4E

## Option 2: Installation Script (UNIX Only)

### 1. **Clone the Repository**:
```bash
   git clone https://github.com/pmer/tla-bin.git
```
### 2. Navigate to the Directory:
```bash
cd tla - bin
```
### 3. Download the Nightly Build:
```bash
sh download_or_update_tla . sh -- nightly
```
### 4. Install

- If installing locally:
```bash
sh install . sh ~/. local
```
- Or, if you have sudo access:
```bash
sudo install . sh
```
### 5. Run:
- Navigate to the binary directory:
  ```bash cd ~/. local / bin ```
- Execute the REPL:
  ```bash ./ tlarepl ```
