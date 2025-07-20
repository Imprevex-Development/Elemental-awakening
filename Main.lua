-- Улучшенный Auto Click Script для FannyFay123 (Xeno Executor)
-- Множественные методы эмуляции кликов для максимальной совместимости

local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local VirtualInputManager = game:GetService("VirtualInputManager")
local UserInputService = game:GetService("UserInputService")
local GuiService = game:GetService("GuiService")
local TweenService = game:GetService("TweenService")
local TeleportService = game:GetService("TeleportService")
local HttpService = game:GetService("HttpService")

local targetPlayer = "FannyDay123"
local player = Players.LocalPlayer

-- Проверяем, что это нужный игрок
if player.Name ~= targetPlayer then
    return
end

-- Переменные для реконнекта
local currentJobId = game.JobId
local currentPlaceId = game.PlaceId
local reconnectEnabled = true

-- Анти-АФК система
local lastActivityTime = tick()
local afkCheckInterval = 15 -- Проверяем каждые 15 секунд
local antiAfkEnabled = true

-- Функция анти-АФК
local function performAntiAfk()
    if not antiAfkEnabled then return end
    
    pcall(function()
        -- Метод 1: Движение мыши
        local mouse = player:GetMouse()
        local centerX = workspace.CurrentCamera.ViewportSize.X / 2
        local centerY = workspace.CurrentCamera.ViewportSize.Y / 2
        local randomX = centerX + math.random(-50, 50)
        local randomY = centerY + math.random(-50, 50)
        VirtualInputManager:SendMouseMoveEvent(randomX, randomY, game)
        
        -- Метод 2: Нажатие случайных клавиш (безопасных)
        local safeKeys = {
            Enum.KeyCode.LeftShift,
            Enum.KeyCode.RightShift,
            Enum.KeyCode.LeftControl,
            Enum.KeyCode.RightControl
        }
        local randomKey = safeKeys[math.random(1, #safeKeys)]
        VirtualInputManager:SendKeyEvent(true, randomKey, false, game)
        task.wait(0.1)
        VirtualInputManager:SendKeyEvent(false, randomKey, false, game)
        
        -- Метод 3: Минимальное движение камеры
        local camera = workspace.CurrentCamera
        if camera and camera.CameraType == Enum.CameraType.Custom then
            local humanoid = player.Character and player.Character:FindFirstChild("Humanoid")
            if humanoid and humanoid.RootPart then
                local currentCFrame = camera.CFrame
                local newCFrame = currentCFrame * CFrame.Angles(math.rad(math.random(-1, 1)), math.rad(math.random(-1, 1)), 0)
                camera.CFrame = newCFrame
                task.wait(0.1)
                camera.CFrame = currentCFrame
            end
        end
        
        lastActivityTime = tick()
    end)
end

-- Функция для автоматического реконнекта
local function attemptReconnect()
    if not reconnectEnabled then return end
    
    pcall(function()
        -- Пытаемся переподключиться к тому же серверу
        TeleportService:TeleportToPlaceInstance(currentPlaceId, currentJobId, player)
    end)
    
    -- Если не получилось подключиться к тому же серверу, подключаемся к любому
    task.wait(5)
    pcall(function()
        TeleportService:Teleport(currentPlaceId, player)
    end)
end

-- Обработчик отключения от сервера
local function onPlayerRemoving()
    if reconnectEnabled then
        task.wait(2) -- Небольшая задержка
        attemptReconnect()
    end
end

-- Обработчик ошибок телепортации
local function onTeleportInitFailed(player, teleportResult, errorMessage)
    if reconnectEnabled then
        task.wait(3)
        attemptReconnect()
    end
end

-- Подключаем обработчики реконнекта
Players.PlayerRemoving:Connect(onPlayerRemoving)
TeleportService.TeleportInitFailed:Connect(onTeleportInitFailed)

-- Защита от кика
game.Players.PlayerRemoving:Connect(function(removedPlayer)
    if removedPlayer == player and reconnectEnabled then
        attemptReconnect()
    end
end)

-- Мониторинг статуса подключения
spawn(function()
    while reconnectEnabled do
        task.wait(30) -- Проверяем каждые 30 секунд
        
        -- Проверяем, подключены ли мы еще
        pcall(function()
            local testConnection = game:GetService("ReplicatedStorage")
            if not testConnection or not game.Players.LocalPlayer then
                attemptReconnect()
            end
        end)
    end
end)

-- Запуск анти-АФК системы
spawn(function()
    while antiAfkEnabled do
        task.wait(afkCheckInterval)
        
        local timeSinceLastActivity = tick() - lastActivityTime
        
        -- Если прошло более 10 минут без активности, выполняем анти-АФК действия
        if timeSinceLastActivity > 600 then
            performAntiAfk()
        end
        
        -- В любом случае периодически выполняем анти-АФК
        if math.random(1, 4) == 1 then -- 25% шанс
            performAntiAfk()
        end
    end
end)

-- Функция для комплексной эмуляции клика (несколько методов одновременно)
local function advancedClick(guiObject)
    if not guiObject or not guiObject.Parent or not guiObject.Visible then
        return false
    end
    
    local success = false
    
    -- Метод 1: VirtualInputManager с точной позицией
    pcall(function()
        local absolutePosition = guiObject.AbsolutePosition
        local absoluteSize = guiObject.AbsoluteSize
        local centerX = absolutePosition.X + absoluteSize.X / 2
        local centerY = absolutePosition.Y + absoluteSize.Y / 2
        
        -- Быстрые клики без задержек
        VirtualInputManager:SendMouseButtonEvent(centerX, centerY, 0, true, guiObject, 1)
        VirtualInputManager:SendMouseButtonEvent(centerX, centerY, 0, false, guiObject, 1)
        success = true
    end)
    
    -- Метод 2: Прямая активация события MouseButton1Click через connections
    pcall(function()
        -- Вызываем событие MouseButton1Down
        if guiObject.MouseButton1Down then
            guiObject.MouseButton1Down:Fire()
        end
        
        -- Вызываем событие MouseButton1Up  
        if guiObject.MouseButton1Up then
            guiObject.MouseButton1Up:Fire()
        end
        
        -- Вызываем событие MouseButton1Click
        if guiObject.MouseButton1Click then
            guiObject.MouseButton1Click:Fire()
        end
        
        success = true
    end)
    
    -- Метод 3: Симуляция через GuiService
    pcall(function()
        -- Устанавливаем фокус на объект
        GuiService.SelectedObject = guiObject
        
        -- Эмулируем нажатие Enter (активация выбранного объекта)
        VirtualInputManager:SendKeyEvent(true, Enum.KeyCode.Return, false, game)
        VirtualInputManager:SendKeyEvent(false, Enum.KeyCode.Return, false, game)
        
        success = true
    end)
    
    -- Метод 4: Изменение свойств кнопки для имитации нажатия
    pcall(function()
        if guiObject:IsA("TextButton") or guiObject:IsA("ImageButton") then
            local originalTransparency = guiObject.BackgroundTransparency
            local originalSize = guiObject.Size
            
            -- Быстрая визуальная обратная связь
            guiObject.BackgroundTransparency = math.max(0, originalTransparency - 0.2)
            guiObject.Size = UDim2.new(originalSize.X.Scale * 0.95, originalSize.X.Offset * 0.95, 
                                      originalSize.Y.Scale * 0.95, originalSize.Y.Offset * 0.95)
            
            -- Мгновенное восстановление свойств
            guiObject.BackgroundTransparency = originalTransparency
            guiObject.Size = originalSize
            
            success = true
        end
    end)
    
    -- Метод 5: Дополнительная симуляция через mouse events
    pcall(function()
        local absolutePosition = guiObject.AbsolutePosition
        local absoluteSize = guiObject.AbsoluteSize
        local centerX = absolutePosition.X + absoluteSize.X / 2
        local centerY = absolutePosition.Y + absoluteSize.Y / 2
        
        -- Перемещаем мышь к кнопке и кликаем
        VirtualInputManager:SendMouseMoveEvent(centerX, centerY, game)
        VirtualInputManager:SendMouseButtonEvent(centerX, centerY, 0, true, game, 1)
        VirtualInputManager:SendMouseButtonEvent(centerX, centerY, 0, false, game, 1)
        
        success = true
    end)
    
    return success
end

-- Функция для поиска и нажатия PlayButton
local function findAndClickPlayButton()
    local playerGui = player:WaitForChild("PlayerGui", 5)
    if not playerGui then
        return false
    end
    
    -- Расширенный поиск по всем возможным путям
    for _, gui in pairs(playerGui:GetChildren()) do
        if gui:IsA("ScreenGui") or gui:IsA("BillboardGui") then
            -- Прямой поиск фрейма Start
            local startFrame = gui:FindFirstChild("Start")
            if startFrame then
                local playButton = startFrame:FindFirstChild("PlayButton")
                if playButton and (playButton:IsA("TextButton") or playButton:IsA("ImageButton")) then
                    if playButton.Visible and playButton.Parent then
                        return advancedClick(playButton)
                    end
                end
            end
            
            -- Рекурсивный поиск на случай вложенности
            local function searchRecursive(parent, depth)
                if depth > 5 then return nil end -- Ограничиваем глубину поиска
                
                for _, child in pairs(parent:GetChildren()) do
                    if child.Name == "Start" and child:IsA("Frame") then
                        local button = child:FindFirstChild("PlayButton")
                        if button then
                            return button
                        end
                    end
                    
                    if child:IsA("GuiObject") then
                        local result = searchRecursive(child, depth + 1)
                        if result then return result end
                    end
                end
                return nil
            end
            
            local foundButton = searchRecursive(gui, 0)
            if foundButton and (foundButton:IsA("TextButton") or foundButton:IsA("ImageButton")) then
                if foundButton.Visible and foundButton.Parent then
                    return advancedClick(foundButton)
                end
            end
        end
    end
    
    return false
end

-- Глобальные переменные для контроля инструментов
local toolConnections = {}
local activeTools = {}
local toolSpamActive = false

-- НОВЫЕ ПЕРЕМЕННЫЕ ДЛЯ СИСТЕМЫ СМЕНЫ ИНСТРУМЕНТОВ
local toolCyclingActive = false
local toolCyclingConnection = nil
local currentToolIndex = 1
local toolSwitchInterval = 1 -- Интервал смены инструментов в секундах

-- Функция для остановки спама инструментов
local function stopToolSpam()
    toolSpamActive = false
    
    for toolName, connection in pairs(toolConnections) do
        if connection then
            connection:Disconnect()
            toolConnections[toolName] = nil
        end
    end
    
    activeTools = {}
end

-- НОВАЯ ФУНКЦИЯ: Остановка системы смены инструментов
local function stopToolCycling()
    toolCyclingActive = false
    
    if toolCyclingConnection then
        toolCyclingConnection:Disconnect()
        toolCyclingConnection = nil
    end
end

-- НОВАЯ ФУНКЦИЯ: Получение всех доступных инструментов
local function getAllAvailableTools()
    local tools = {}
    
    local backpack = player:FindFirstChild("Backpack")
    if backpack then
        for _, item in pairs(backpack:GetChildren()) do
            if item:IsA("Tool") then
                table.insert(tools, item)
            end
        end
    end
    
    local character = player.Character
    if character then
        for _, item in pairs(character:GetChildren()) do
            if item:IsA("Tool") then
                table.insert(tools, item)
            end
        end
    end
    
    return tools
end

-- НОВАЯ ФУНКЦИЯ: Активация системы автоматической смены инструментов
local function startToolCycling()
    -- Останавливаем предыдущую систему смены
    stopToolCycling()
    
    toolCyclingActive = true
    
    toolCyclingConnection = task.spawn(function()
        while toolCyclingActive do
            local character = player.Character
            if character then
                local humanoid = character:FindFirstChild("Humanoid")
                if humanoid then
                    local allTools = getAllAvailableTools()
                    
                    -- Проверяем, есть ли у нас 2+ инструмента
                    if #allTools >= 2 then
                        -- Находим текущий экипированный инструмент
                        local currentEquippedTool = nil
                        for _, item in pairs(character:GetChildren()) do
                            if item:IsA("Tool") then
                                currentEquippedTool = item
                                break
                            end
                        end
                        
                        -- Если есть экипированный инструмент, снимаем его
                        if currentEquippedTool then
                            pcall(function()
                                humanoid:UnequipTools()
                            end)
                            task.wait(0.1)
                        end
                        
                        -- Выбираем следующий инструмент для экипировки
                        local backpackTools = {}
                        local backpack = player:FindFirstChild("Backpack")
                        if backpack then
                            for _, item in pairs(backpack:GetChildren()) do
                                if item:IsA("Tool") then
                                    table.insert(backpackTools, item)
                                end
                            end
                        end
                        
                        if #backpackTools > 0 then
                            -- Циклично выбираем инструмент
                            if currentToolIndex > #backpackTools then
                                currentToolIndex = 1
                            end
                            
                            local toolToEquip = backpackTools[currentToolIndex]
                            if toolToEquip then
                                pcall(function()
                                    humanoid:EquipTool(toolToEquip)
                                end)
                                
                                -- Ждем завершения экипировки
                                for i = 1, 10 do
                                    task.wait(0.05)
                                    if toolToEquip.Parent == character then
                                        break
                                    end
                                end
                                
                                -- Спамим активацией нового инструмента
                                local spamDuration = toolSwitchInterval * 0.8 -- Спамим 80% времени до смены
                                local spamStart = tick()
                                
                                while toolCyclingActive and (tick() - spamStart) < spamDuration do
                                    if toolToEquip.Parent == character then
                                        -- Множественная активация инструмента
                                        pcall(function()
                                            toolToEquip:Activate()
                                        end)
                                        
                                        -- Спам кликов
                                        pcall(function()
                                            local camera = workspace.CurrentCamera
                                            local centerX = camera.ViewportSize.X / 2
                                            local centerY = camera.ViewportSize.Y / 2
                                            VirtualInputManager:SendMouseButtonEvent(centerX, centerY, 0, true, game, 1)
                                            VirtualInputManager:SendMouseButtonEvent(centerX, centerY, 0, false, game, 1)
                                        end)
                                        
                                        -- Активация RemoteEvent/RemoteFunction
                                        pcall(function()
                                            for _, descendant in pairs(toolToEquip:GetDescendants()) do
                                                if descendant:IsA("RemoteEvent") then
                                                    descendant:FireServer()
                                                elseif descendant:IsA("RemoteFunction") then
                                                    spawn(function()
                                                        pcall(function()
                                                            descendant:InvokeServer()
                                                        end)
                                                    end)
                                                end
                                            end
                                        end)
                                        
                                        -- Активация ClickDetector'ов
                                        pcall(function()
                                            for _, descendant in pairs(toolToEquip:GetDescendants()) do
                                                if descendant:IsA("ClickDetector") then
                                                    for _, connection in pairs(getconnections(descendant.MouseClick)) do
                                                        if connection and connection.Function then
                                                            spawn(function()
                                                                pcall(function()
                                                                    connection.Function(player)
                                                                end)
                                                            end)
                                                        end
                                                    end
                                                end
                                            end
                                        end)
                                    end
                                    
                                    task.wait(0.01) -- Очень частый спам
                                end
                            end
                            
                            currentToolIndex = currentToolIndex + 1
                        end
                    end
                end
            end
            
            -- Ждем до следующей смены инструмента
            task.wait(toolSwitchInterval)
        end
    end)
end

-- Функция для спам-активации конкретного инструмента
local function spamActivateTool(tool)
    if not tool then
        return
    end
    
    local toolName = tool.Name
    
    -- Останавливаем предыдущее соединение для этого инструмента
    if toolConnections[toolName] then
        toolConnections[toolName]:Disconnect()
    end
    
    -- Создаем новое соединение для постоянной активации
    toolConnections[toolName] = RunService.Heartbeat:Connect(function()
        if not toolSpamActive or not tool or not tool.Parent then
            return
        end
        
        pcall(function()
            local character = player.Character
            if not character then return end
            
            -- Проверяем, что инструмент экипирован
            if tool.Parent == character then
                -- Метод 1: Прямая активация инструмента (основной метод)
                pcall(function()
                    tool:Activate()
                end)
                
                -- Метод 2: Спам кликов через VirtualInputManager
                pcall(function()
                    local camera = workspace.CurrentCamera
                    local centerX = camera.ViewportSize.X / 2
                    local centerY = camera.ViewportSize.Y / 2
                    
                    -- Быстрый спам кликов
                    VirtualInputManager:SendMouseButtonEvent(centerX, centerY, 0, true, game, 1)
                    VirtualInputManager:SendMouseButtonEvent(centerX, centerY, 0, false, game, 1)
                end)
                
                -- Метод 3: Активация через события инструмента
                pcall(function()
                    if tool.Activated then
                        for _, connection in pairs(getconnections(tool.Activated)) do
                            if connection and connection.Function then
                                connection.Function()
                            end
                        end
                    end
                end)
                
                -- Метод 4: Активация RemoteEvent/RemoteFunction
                pcall(function()
                    for _, descendant in pairs(tool:GetDescendants()) do
                        if descendant:IsA("RemoteEvent") then
                            descendant:FireServer()
                        elseif descendant:IsA("RemoteFunction") then
                            spawn(function()
                                pcall(function()
                                    descendant:InvokeServer()
                                end)
                            end)
                        end
                    end
                end)
                
                -- Метод 5: Активация ClickDetector'ов
                pcall(function()
                    for _, descendant in pairs(tool:GetDescendants()) do
                        if descendant:IsA("ClickDetector") then
                            for _, connection in pairs(getconnections(descendant.MouseClick)) do
                                if connection and connection.Function then
                                    spawn(function()
                                        pcall(function()
                                            connection.Function(player)
                                        end)
                                    end)
                                end
                            end
                        end
                    end
                end)
                
                -- Метод 6: Handle активация (если есть Handle)
                pcall(function()
                    local handle = tool:FindFirstChild("Handle")
                    if handle then
                        for _, descendant in pairs(handle:GetDescendants()) do
                            if descendant:IsA("ClickDetector") then
                                for _, connection in pairs(getconnections(descendant.MouseClick)) do
                                    if connection and connection.Function then
                                        spawn(function()
                                            pcall(function()
                                                connection.Function(player)
                                            end)
                                        end)
                                    end
                                end
                            end
                        end
                    end
                end)
            end
        end)
    end)
    
    activeTools[toolName] = tool
end

-- МОДИФИЦИРОВАННАЯ ФУНКЦИЯ: Постоянная активация всех инструментов с поддержкой автосмены
local function activateToolsConstantly()
    -- Сначала останавливаем предыдущую активацию и систему смены
    stopToolSpam()
    stopToolCycling()
    
    local backpack = player:WaitForChild("Backpack", 5)
    if not backpack then
        return
    end
    
    local character = player.Character
    if not character then
        return
    end
    
    local humanoid = character:WaitForChild("Humanoid", 5)
    if not humanoid then
        return
    end
    
    -- Получаем все инструменты
    local backpackTools = {}
    for _, item in pairs(backpack:GetChildren()) do
        if item:IsA("Tool") then
            table.insert(backpackTools, item)
        end
    end
    
    local equippedTools = {}
    for _, item in pairs(character:GetChildren()) do
        if item:IsA("Tool") then
            table.insert(equippedTools, item)
        end
    end
    
    local totalTools = #backpackTools + #equippedTools
    
    if totalTools == 0 then
        return
    end
    
    -- НОВАЯ ЛОГИКА: Проверяем количество инструментов
    if totalTools >= 2 then
        -- Если у нас 2+ инструмента, запускаем систему автоматической смены
        startToolCycling()
    else
        -- Если у нас только 1 инструмент, используем старую систему постоянного спама
        toolSpamActive = true
        
        -- Сначала запускаем спам для уже экипированных инструментов
        for _, tool in pairs(equippedTools) do
            spamActivateTool(tool)
        end
        
        -- Теперь экипируем и активируем инструменты из рюкзака
        for i, tool in pairs(backpackTools) do
            task.spawn(function()
                pcall(function()
                    humanoid:EquipTool(tool)
                    
                    for attempts = 1, 20 do
                        task.wait(0.05)
                        if tool.Parent == character then
                            break
                        elseif attempts == 20 then
                            return
                        end
                    end
                    
                    if tool.Parent == character then
                        spamActivateTool(tool)
                    end
                end)
            end)
            
            task.wait(0.1)
        end
    end
end

-- Мониторинг новых инструментов
local function startToolMonitoring()
    local backpack = player:WaitForChild("Backpack", 5)
    if backpack then
        backpack.ChildAdded:Connect(function(child)
            if child:IsA("Tool") and (toolSpamActive or toolCyclingActive) then
                task.wait(0.1)
                -- Перезапускаем систему активации с учетом нового инструмента
                activateToolsConstantly()
            end
        end)
        
        -- НОВЫЙ ОБРАБОТЧИК: Мониторинг удаления инструментов
        backpack.ChildRemoved:Connect(function(child)
            if child:IsA("Tool") and (toolSpamActive or toolCyclingActive) then
                task.wait(0.1)
                activateToolsConstantly()
            end
        end)
    end
    
    -- Мониторинг смены персонажа
    player.CharacterAdded:Connect(function(character)
        if toolSpamActive or toolCyclingActive then
            task.wait(2) -- Ждем полной загрузки персонажа
            activateToolsConstantly() -- Перезапускаем активацию инструментов
        end
    end)
end

-- Основной цикл мониторинга
local lastCheckTime = 0
local checkInterval = 1 -- Проверяем каждую секунду для быстрого реагирования

local connection
connection = RunService.Heartbeat:Connect(function()
    local currentTime = tick()
    
    if currentTime - lastCheckTime >= checkInterval then
        lastCheckTime = currentTime
        
        -- Проверяем наличие PlayButton и кликаем его
        local success = findAndClickPlayButton()
        if success then
            task.wait(2) -- Даем время на обработку клика
            
            -- После успешного клика активируем инструменты в режиме постоянного спама
            activateToolsConstantly()
            
            -- Увеличиваем интервал после успешного выполнения
            checkInterval = 5
        end
    end
end)

-- МОДИФИЦИРОВАННАЯ ФУНКЦИЯ: Остановка скрипта с учетом новой системы
local function stopScript()
    if connection then
        connection:Disconnect()
        connection = nil
    end
    stopToolSpam() -- Останавливаем спам инструментов
    stopToolCycling() -- Останавливаем систему смены инструментов
    reconnectEnabled = false -- Отключаем реконнект
    antiAfkEnabled = false -- Отключаем анти-АФК
end

-- МОДИФИЦИРОВАННЫЕ ОБРАБОТЧИКИ КЛАВИШ: Добавлены новые горячие клавиши
UserInputService.InputBegan:Connect(function(input)
    -- Обновляем время активности при любом вводе
    lastActivityTime = tick()
    
    if input.KeyCode == Enum.KeyCode.End then
        stopScript()
    elseif input.KeyCode == Enum.KeyCode.Home then
        -- Manual trigger на клавишу HOME
        findAndClickPlayButton()
    elseif input.KeyCode == Enum.KeyCode.Delete then
        -- Остановка спама инструментов и системы смены
        stopToolSpam()
        stopToolCycling()
    elseif input.KeyCode == Enum.KeyCode.Insert then
        -- Ручной запуск активации инструментов (с автоопределением режима)
        activateToolsConstantly()
    elseif input.KeyCode == Enum.KeyCode.PageUp then
        -- Переключение реконнекта
        reconnectEnabled = not reconnectEnabled
    elseif input.KeyCode == Enum.KeyCode.PageDown then
        -- Переключение анти-АФК
        antiAfkEnabled = not antiAfkEnabled
    elseif input.KeyCode == Enum.KeyCode.F1 then
        -- Ручной реконнект
        attemptReconnect()
    elseif input.KeyCode == Enum.KeyCode.F2 then
        -- НОВАЯ ГОРЯЧАЯ КЛАВИША: Переключение режима смены инструментов
        if toolCyclingActive then
            stopToolCycling()
        else
            local allTools = getAllAvailableTools()
            if #allTools >= 2 then
                startToolCycling()
            end
        end
    elseif input.KeyCode == Enum.KeyCode.F3 then
        -- НОВАЯ ГОРЯЧАЯ КЛАВИША: Изменение интервала смены инструментов
        if toolSwitchInterval == 1 then
            toolSwitchInterval = 0.5 -- Быстрее
        elseif toolSwitchInterval == 0.5 then
            toolSwitchInterval = 2 -- Медленнее
        else
            toolSwitchInterval = 1 -- Обычно
        end
    end
end)

-- Запускаем мониторинг инструментов
startToolMonitoring()

-- РАСШИРЕННЫЙ ОБЪЕКТ УПРАВЛЕНИЯ: Добавлены новые функции
return {
    stop = stopScript,
    clickButton = findAndClickPlayButton,
    activateTools = activateToolsConstantly,
    stopToolSpam = stopToolSpam,
    testClick = function(obj) return advancedClick(obj) end,
    toggleReconnect = function() reconnectEnabled = not reconnectEnabled end,
    toggleAntiAfk = function() antiAfkEnabled = not antiAfkEnabled end,
    reconnect = attemptReconnect,
    antiAfk = performAntiAfk,
    -- НОВЫЕ ФУНКЦИИ ДЛЯ СИСТЕМЫ СМЕНЫ ИНСТРУМЕНТОВ
    startToolCycling = startToolCycling,
    stopToolCycling = stopToolCycling,
    toggleToolCycling = function() 
        if toolCyclingActive then 
            stopToolCycling() 
        else 
            local allTools = getAllAvailableTools()
            if #allTools >= 2 then
                startToolCycling()
            end
        end 
    end,
    setToolSwitchInterval = function(interval) 
        if type(interval) == "number" and interval > 0 then
            toolSwitchInterval = interval
        end
    end,
    getToolSwitchInterval = function() return toolSwitchInterval end,
    getActiveMode = function() 
        if toolCyclingActive then
            return "cycling"
        elseif toolSpamActive then
            return "spam"
        else
            return "inactive"
        end
    end,
    getToolCount = function() return #getAllAvailableTools() end,
    getAllTools = getAllAvailableTools
}
