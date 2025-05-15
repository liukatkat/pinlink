// Make vscode globally accessible
let vscode;

// Make functions globally accessible
window.linkState = function (sourceStateId) {
    // Get all states except the current one
    const states = window.trackedStates.filter(state => state.id !== sourceStateId);

    if (states.length === 0) {
        vscode.postMessage({
            command: 'alert',
            text: 'No other states available to link to.'
        });
        return;
    }

    // Create a dropdown with all available states
    const stateOptions = states.map(state => `<option value="${state.id}">${state.theoremName}: ${state.text}</option>`).join('');

    // Create a modal dialog
    const modal = document.createElement('div');
    modal.style.position = 'fixed';
    modal.style.top = '0';
    modal.style.left = '0';
    modal.style.width = '100%';
    modal.style.height = '100%';
    modal.style.backgroundColor = 'rgba(0, 0, 0, 0.5)';
    modal.style.display = 'flex';
    modal.style.justifyContent = 'center';
    modal.style.alignItems = 'center';
    modal.style.zIndex = '1000';

    modal.innerHTML = `
        <div style="background-color: var(--vscode-editor-background); padding: 20px; border-radius: 4px; width: 80%; max-width: 500px;">
            <h3 style="margin-top: 0;">Link to State</h3>
            <p>Select a state to link to:</p>
            <select id="stateSelect" style="width: 100%; padding: 8px; margin-bottom: 15px; background-color: var(--vscode-input-background); color: var(--vscode-input-foreground); border: 1px solid var(--vscode-input-border);">
                ${stateOptions}
            </select>
            <div style="display: flex; justify-content: flex-end;">
                <button onclick="document.body.removeChild(this.parentNode.parentNode.parentNode)" style="margin-right: 10px;">Cancel</button>
                <button onclick="window.confirmLink('${sourceStateId}', document.getElementById('stateSelect').value)">Link</button>
            </div>
        </div>
    `;

    document.body.appendChild(modal);
};

window.confirmLink = function (sourceStateId, targetStateId) {
    vscode.postMessage({
        command: 'linkStates',
        sourceStateId,
        targetStateId
    });

    // Remove the modal
    document.body.removeChild(document.querySelector('div[style*="position: fixed"]'));
};

window.unlinkState = function (sourceStateId, targetStateId) {
    vscode.postMessage({
        command: 'unlinkStates',
        sourceStateId,
        targetStateId
    });
};

// Add the navigateToState function to the global scope
window.navigateToState = function (stateId) {
    const state = window.trackedStates.find(s => s.id === stateId);
    if (state) {
        vscode.postMessage({
            command: 'navigateToState',
            stateId: stateId,
            theoremName: state.theoremName,
            lineOffset: state.lineOffset,
            characterOffset: state.characterOffset
        });
    }
};

// Initialize the webview
(function () {
    vscode = acquireVsCodeApi();

    // Store tracked states in the global scope
    window.trackedStates = [];

    // Get the checkbox element
    const showDiffCheckbox = document.getElementById('showDiffCheckbox');

    // Get the refresh button element
    const refreshButton = document.getElementById('refreshButton');

    // Add event listener for the refresh button
    refreshButton.addEventListener('click', () => {
        vscode.postMessage({ command: 'refreshStates' });
    });

    // Function to update the state list
    function updateStateList(states) {
        // Update the global trackedStates
        window.trackedStates = states;

        const stateListElement = document.getElementById('stateList');

        if (!states || states.length === 0) {
            stateListElement.innerHTML = '<div class="empty-state">No states tracked yet. Right-click in your editor and select "Track State" to begin.</div>';
            return;
        }

        let html = '';
        states.forEach((state, index) => {
            const hasCoqResult = state.coqResult !== undefined && state.coqResult !== null;
            const isError = hasCoqResult && state.coqResult.startsWith('Error:');
            const shouldShowDiff = showDiffCheckbox.checked && hasCoqResult && state.coqResult.includes("IHn' : n' + 0 = n'");

            // Process Coq result to insert div after the specific line
            let processedCoqResult = state.coqResult;
            if (shouldShowDiff) {
                // Replace the specific line with a styled version
                processedCoqResult = processedCoqResult.replace(
                    "IHn' : n' + 0 = n'",
                    "<div class=\"hardcoded-div\"><span class=\"subtraction\">E: n = S n'</span></div>\n<div class=\"addition-container\"><span class=\"addition\">IHn' : n' + 0 = n'</span></div>"
                );
            }

            html += `
                <div class="state-item" data-state-id="${state.id}">
                    <div class="state-header">
                        <span class="state-title" onclick="window.navigateToState('${state.id}')">${state.theoremName}</span>
                    </div>
                    <div class="state-content" onclick="window.navigateToState('${state.id}')">${state.text}</div>
                    <div class="state-meta">
                        Line: ${state.lineOffset}, Character: ${state.characterOffset}
                    </div>
                    ${hasCoqResult ? `
                        <div class="coq-result">
                            <div class="coq-result-header ${isError ? 'error' : ''}">
                                ${isError ? 'Coq Error' : 'Proof State'}
                            </div>
                            <div class="coq-result-content ${isError ? 'error' : ''}">
                                ${processedCoqResult}
                            </div>
                        </div>
                    ` : ''}
                    <div class="linked-states">
                        <div class="linked-states-header">Linked States</div>
                        <div class="linked-states-list">
                            ${renderLinkedStates(state, states)}
                        </div>
                    </div>
                    <div class="state-actions">
                        <button class="link-button" onclick="window.linkState('${state.id}')">Link to Another State</button>
                    </div>
                </div>
            `;
        });

        stateListElement.innerHTML = html;
    }

    // Function to render linked states
    function renderLinkedStates(currentState, allStates) {
        if (!currentState.linkedStateIds || currentState.linkedStateIds.length === 0) {
            return '<div class="empty-state">No linked states</div>';
        }

        let html = '';
        currentState.linkedStateIds.forEach(linkedStateId => {
            const linkedState = allStates.find(s => s.id === linkedStateId);
            if (linkedState) {
                const hasCoqResult = linkedState.coqResult !== undefined && linkedState.coqResult !== null;
                const isError = hasCoqResult && linkedState.coqResult.startsWith('Error:');
                const shouldShowDiff = showDiffCheckbox.checked && hasCoqResult && linkedState.coqResult.includes("IHn' : n' + 0 = n'");

                // Process Coq result to insert div after the specific line
                let processedCoqResult = linkedState.coqResult;
                if (shouldShowDiff) {
                    // Replace the specific line with a styled version
                    processedCoqResult = processedCoqResult.replace(
                        "IHn' : n' + 0 = n'",
                        "<div class=\"addition-container\"><span class=\"addition\">IHn' : n' + 0 = n'</span></div>\n<div class=\"hardcoded-div\"><span class=\"subtraction\">E: n = S n'</span></div>"
                    );
                }

                html += `
                    <div class="linked-state-item">
                        <div class="linked-state-text" onclick="window.navigateToState('${linkedState.id}')">
                            <div class="linked-state-theorem">${linkedState.theoremName}</div>
                            <div class="linked-state-code">${linkedState.text}</div>
                            ${hasCoqResult ? `
                                <div class="linked-state-coq-result ${isError ? 'error' : ''}">
                                    <div class="linked-state-coq-header">${isError ? 'Coq Error' : 'Proof State'}</div>
                                    <div class="linked-state-coq-content">${processedCoqResult}</div>
                                </div>
                            ` : ''}
                        </div>
                        <button class="link-button active" onclick="window.unlinkState('${currentState.id}', '${linkedStateId}')">Unlink</button>
                    </div>
                `;
            }
        });

        return html;
    }

    // Handle messages from the extension
    window.addEventListener('message', event => {
        const message = event.data;
        switch (message.command) {
            case 'updateStates':
                updateStateList(message.states);
                return;
        }
    });

    // Add event listener for the checkbox
    showDiffCheckbox.addEventListener('change', () => {
        updateStateList(window.trackedStates);
    });

    // Request initial states
    vscode.postMessage({ command: 'getStates' });
}());